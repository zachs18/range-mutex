#![deny(unsafe_op_in_unsafe_fn)]
use parking_lot::Mutex;
#[cfg(feature = "async")]
use std::task::{Poll, Waker};
use std::{
    cell::UnsafeCell,
    cmp::Ordering,
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::{Deref, DerefMut, Range, RangeBounds},
    ptr::NonNull,
    thread::Thread,
};

#[cfg(any(test, doctest))]
mod tests;
mod util;

enum Waiter {
    Thread(Thread),
    #[cfg(feature = "async")]
    Task(Waker),
}

impl Waiter {
    fn unpark(&self) {
        match self {
            Waiter::Thread(thread) => thread.unpark(),
            #[cfg(feature = "async")]
            Waiter::Task(waker) => waker.wake_by_ref(),
        }
    }
}

#[derive(Default)]
struct RangesUsed {
    /// Invariants:
    /// * For each range: `range.len() > 0`
    /// * For each adjacent pair of ranges: `r0.end <= r1.start` (i.e. ranges
    ///   are sorted and do not overlap)
    ///
    /// This allows performing a binary-search on this vec for overlapping
    /// ranges.
    ranges: Vec<Range<usize>>,
    waiting: Vec<(Waiter, Range<usize>)>,
}

struct Locked;
struct NotLocked;

impl RangesUsed {
    const fn new() -> Self {
        Self { ranges: Vec::new(), waiting: Vec::new() }
    }

    fn overlapping_range_idx(
        &self,
        range: &Range<usize>,
    ) -> Result<usize, usize> {
        debug_assert!(
            !range.is_empty(),
            "empty ranges should be handled already"
        );
        self.ranges.binary_search_by(|locked_range| {
            if locked_range.end <= range.start {
                Ordering::Less
            } else if locked_range.start >= range.end {
                Ordering::Greater
            } else {
                // This means the range overlaps
                Ordering::Equal
            }
        })
    }

    /// If `make_waiter` is `None`, no waiter will be inserted.
    fn lock_range(
        &mut self,
        range: &Range<usize>,
        make_waiter: Option<impl FnOnce() -> Waiter>,
    ) -> Result<Locked, NotLocked> {
        let idx = self.overlapping_range_idx(range);
        match idx {
            Ok(_overlapping_range_idx) => {
                if let Some(waiter) = make_waiter {
                    self.waiting.push((waiter(), range.clone()));
                }
                Err(NotLocked)
            }
            Err(insert_idx) => {
                self.ranges.insert(insert_idx, range.clone());
                Ok(Locked)
            }
        }
    }

    fn unlock_range(&mut self, range: &Range<usize>) {
        let (Ok(idx) | Err(idx)) = self.overlapping_range_idx(range);
        debug_assert_eq!(&self.ranges[idx], range, "range is locked");
        self.ranges.remove(idx);
        self.waiting.retain(|(unparker, waiting_range)| {
            // TODO: more precise unpark selection
            // e.g. don't unpark two overlapping waiters,
            // don't unpark a waiter that overlaps with another existing lock.
            let should_unpark_and_remove = util::overlaps(range, waiting_range);
            if should_unpark_and_remove {
                unparker.unpark();
            }
            // return value is should *not* remove
            !should_unpark_and_remove
        })
    }

    fn split_locked_range(
        &mut self,
        range: &Range<usize>,
        mid: usize,
    ) -> (Range<usize>, Range<usize>) {
        debug_assert!(mid <= range.len());
        let (head, tail) =
            (range.start..range.start + mid, range.start + mid..range.end);
        let (Ok(idx) | Err(idx)) = self.overlapping_range_idx(range);
        debug_assert_eq!(&self.ranges[idx], range, "range is locked");
        self.ranges.splice(idx..=idx, [head.clone(), tail.clone()]);
        (head, tail)
    }
}

/// The trait for types which can be used as the backing store for a
/// [`RangeMutex`].
///
/// # Safety:
///
/// * `AsUnsafeCell` must be `Send` and `Sync` if `T` is `Send`.
/// * TODO
pub unsafe trait RangeMutexBackingStorage<T>:
    AsMut<[T]> + AsRef<[T]>
{
    type AsUnsafeCell: AsMut<[UnsafeCell<T>]> + AsRef<[UnsafeCell<T>]>;
    fn into_unsafecell(self) -> Self::AsUnsafeCell;
    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self;
}

unsafe impl<'a, T, const N: usize> RangeMutexBackingStorage<T>
    for &'a mut [T; N]
{
    type AsUnsafeCell = &'a mut [UnsafeCell<T>; N];

    fn into_unsafecell(self) -> Self::AsUnsafeCell {
        util::wrap_unsafecell_slice(self).try_into().unwrap()
    }

    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self {
        util::unwrap_unsafecell_slice(value).try_into().unwrap()
    }
}

unsafe impl<T, const N: usize> RangeMutexBackingStorage<T> for [T; N] {
    type AsUnsafeCell = [UnsafeCell<T>; N];

    fn into_unsafecell(self) -> Self::AsUnsafeCell {
        util::wrap_unsafecell_array(self)
    }

    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self {
        util::unwrap_unsafecell_array(value)
    }
}

unsafe impl<'a, T> RangeMutexBackingStorage<T> for &'a mut [T] {
    type AsUnsafeCell = &'a mut [UnsafeCell<T>];

    fn into_unsafecell(self) -> Self::AsUnsafeCell {
        util::wrap_unsafecell_slice(self)
    }

    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self {
        util::unwrap_unsafecell_slice(value)
    }
}

unsafe impl<T> RangeMutexBackingStorage<T> for Box<[T]> {
    type AsUnsafeCell = Box<[UnsafeCell<T>]>;

    fn into_unsafecell(self) -> Self::AsUnsafeCell {
        util::wrap_unsafecell_vec(self.into_vec()).into_boxed_slice()
    }

    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self {
        util::unwrap_unsafecell_vec(value.into_vec()).into_boxed_slice()
    }
}

unsafe impl<T> RangeMutexBackingStorage<T> for Vec<T> {
    type AsUnsafeCell = Vec<UnsafeCell<T>>;

    fn into_unsafecell(self) -> Self::AsUnsafeCell {
        util::wrap_unsafecell_vec(self)
    }

    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self {
        util::unwrap_unsafecell_vec(value)
    }
}

unsafe impl<'a, T> RangeMutexBackingStorage<T> for RangeMutexGuard<'a, T> {
    type AsUnsafeCell = RangeMutexGuard<'a, UnsafeCell<T>>;

    fn into_unsafecell(self) -> Self::AsUnsafeCell {
        let this = ManuallyDrop::new(self);
        RangeMutexGuard {
            data: NonNull::new(this.data.as_ptr() as _).unwrap(),
            range: this.range.clone(),
            used: this.used,
            _variance: PhantomData,
        }
    }

    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self {
        let this = ManuallyDrop::new(value);
        RangeMutexGuard {
            data: NonNull::new(this.data.as_ptr() as _).unwrap(),
            range: this.range.clone(),
            used: this.used,
            _variance: PhantomData,
        }
    }
}

/// A `Mutex`-like type for slices and slice-like containers.
///
/// This type acts similarly to [`std::sync::Mutex<[T]>`][std::sync::Mutex],
/// except that nonoverlapping ranges of the slice can be locked separately.
///
/// # Example
///
/// ```
/// use std::sync::Arc;
/// use std::thread;
/// use range_mutex::RangeMutex;
///
/// const N: usize = 10;
///
/// // Spawn a few threads to increment ranges of a shared vector (non-atomically).
/// let mut data = RangeMutex::new(vec![0; N + 1]);
///
/// thread::scope(|scope| {
///     let data = &data;
///     for i in 0..N {
///         scope.spawn(move || {
///             // The shared state can only be accessed once the lock is held.
///             // Our non-atomic increment is safe because we're the only thread
///             // which can access our range of the shared state when the lock is held.
///             let mut data = data.lock(i..=i+1);
///             data[0] += 1;
///             data[1] += 1;
///             // the lock is unlocked here when `data` goes out of scope.
///         });
///     }
/// });
///
/// assert_eq!(data.get_mut(), [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1]);
/// ```
///
/// ## Zero-Length Ranges
///
/// Attempts to lock zero-length ranges of a [`RangeMutex`] will always succeed
/// (assuming they are not out-of-bounds). Zero-length ranges are not considered
/// to overlap with any other ranges, including themselves. For example, having
/// a lock on the (half-open) range `2..6` will not block an attempt to lock
/// the (half-open) range `4..4`, and vice versa, since the range `4..4` is
/// zero-length, and thus empty.
pub struct RangeMutex<T, B: RangeMutexBackingStorage<T>> {
    used: Mutex<RangesUsed>,
    data: B::AsUnsafeCell,
}

unsafe impl<T: Send, B: RangeMutexBackingStorage<T> + Sync> Sync
    for RangeMutex<T, B>
{
}
unsafe impl<T: Send, B: RangeMutexBackingStorage<T> + Send> Send
    for RangeMutex<T, B>
{
}

impl<T, B: RangeMutexBackingStorage<T>> RangeMutex<T, B> {
    /// Creates a new `RamgeMutex` in an unlocked state ready for use.
    pub fn new(values: B) -> Self {
        let data = B::into_unsafecell(values);

        Self { data, used: Mutex::new(RangesUsed::new()) }
    }

    /// Consumes this `RangeMutex`, returning the underlying data
    pub fn into_inner(self) -> B {
        B::from_unsafecell(self.data)
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the Mutex mutably, no actual locking needs to
    /// take place – the mutable borrow statically guarantees no locks exist.
    pub fn get_mut(&mut self) -> &mut [T] {
        util::unwrap_unsafecell_slice(self.data.as_mut())
    }

    /// Undo the effect of leaked guards on the borrow state of the
    /// `RangeMutex`.
    ///
    /// This call is similar to [`get_mut`] but more specialized. It borrows
    /// `RangeMutex` mutably to ensure no locks exist and then resets the
    /// state tracking locks. This is relevant if some `RangeMutexGuard`s have
    /// been leaked.
    pub fn undo_leak(&mut self) -> &mut [T] {
        let used = self.used.get_mut();
        used.ranges.clear();
        used.waiting.clear();
        self.get_mut()
    }

    /// Attempts to acquire a lock for a range of this slice.
    ///
    /// If the lock could not be acquired at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the slice.
    pub fn try_lock(
        &self,
        range: impl RangeBounds<usize>,
    ) -> Option<RangeMutexGuard<'_, T>> {
        // panics if out of range
        let range = util::range(self.data.as_ref().len(), range);
        if range.is_empty() {
            return Some(RangeMutexGuard::empty());
        }
        let mut used = self.used.lock();

        match used.lock_range(&range, None::<fn() -> Waiter>) {
            Err(NotLocked) => None,
            Ok(Locked) => {
                let data = &self.data.as_ref()[range.clone()];
                let data = util::transpose_unsafecell_slice(data);
                Some(RangeMutexGuard {
                    data: NonNull::new(data.get()).unwrap(),
                    range,
                    used: Some(&self.used),
                    _variance: PhantomData,
                })
            }
        }
    }

    /// Acquires a lock for a range of this slice, blocking the current thread
    /// until it is able to do so.
    ///
    /// This function will block the local thread until it is available to
    /// acquire the lock. Upon returning, the thread is the only thread with
    /// the lock held for the given range. An RAII guard is returned to allow
    /// scoped unlock of the lock. When the guard goes out of scope, the
    /// lock will be unlocked.
    ///
    /// The exact behavior on locking a range in a thread which already holds
    /// a lock on an overlapping range is left unspecified. However, this
    /// function will not return on the second call (it might panic or
    /// deadlock, for example).
    ///
    /// Mutual attempts between mutiple threads to lock overlapping ranges may
    /// result in a deadlock. To avoid this, have all threads lock ranges in
    /// ascending or descending order consistently.
    ///
    /// ```rust,ignore
    /// # use range_mutex::RangeMutex;
    /// # let mutex = RangeMutex::new(vec![0; 8]);
    /// # std::thread::scope(|scope| {
    /// #  scope.spawn(|| {
    /// // Thread 1:
    /// let _g1 = mutex.lock(0..=2);
    /// let _g2 = mutex.lock(3..=5); // Thread 1 may deadlock here if thread 1 holds 0..=2 and thread 2 holds 4..=7.
    /// #  });
    ///
    /// #  scope.spawn(|| {
    /// // Thread 2:
    /// let _g1 = mutex.lock(4..=7);
    /// let _g2 = mutex.lock(0..=3); // Thread 2 may deadlock here if thread 1 holds 0..=2 and thread 2 holds 4..=7.
    /// #  });
    /// # });
    /// ```
    ///
    /// ```rust
    /// # use range_mutex::RangeMutex;
    /// # let mutex = RangeMutex::new(vec![0; 8]);
    /// # std::thread::scope(|scope| {
    /// #  scope.spawn(|| {
    /// // Thread 1:
    /// let _g1 = mutex.lock(0..=2); // Either thread 1 will get 0..=2 first, or thread 2 will get 0..=3 first, and then that thread will continue.
    /// let _g2 = mutex.lock(3..=5);
    /// #  });
    ///
    /// #  scope.spawn(|| {
    /// // Thread 2:
    /// let _g1 = mutex.lock(0..=3); // Either thread 1 will get 0..=2 first, or thread 2 will get 0..=3 first, and then that thread will continue.
    /// let _g2 = mutex.lock(4..=7);
    /// #  });
    /// # });
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the slice.
    pub fn lock(
        &self,
        range: impl RangeBounds<usize>,
    ) -> RangeMutexGuard<'_, T> {
        // panics if out of range
        let range = util::range(self.data.as_ref().len(), range);
        if range.is_empty() {
            return RangeMutexGuard::empty();
        }
        let mut used = self.used.lock();
        loop {
            match used.lock_range(
                &range,
                Some(|| Waiter::Thread(std::thread::current())),
            ) {
                Err(NotLocked) => {
                    // Don't hold the mutex while parked
                    drop(used);
                    std::thread::park();
                    used = self.used.lock();
                }
                Ok(Locked) => {
                    let data = &self.data.as_ref()[range.clone()];
                    let data = util::transpose_unsafecell_slice(data);
                    return RangeMutexGuard {
                        data: NonNull::new(data.get()).unwrap(),
                        range,
                        used: Some(&self.used),
                        _variance: PhantomData,
                    };
                }
            }
        }
    }

    /// Asynchronously acquires a lock for a range of this slice, blocking the
    /// current task until it is able to do so.
    ///
    /// This function will block the local task until it is available to
    /// acquire the lock. Upon returning, the task is the only task with
    /// the lock held for the given range. An RAII guard is returned to allow
    /// scoped unlock of the lock. When the guard goes out of scope, the
    /// lock will be unlocked.
    ///
    /// The exact behavior on locking a range in a task which already holds
    /// a lock on an overlapping range is left unspecified. However, this
    /// function will not return on the second call (it might panic or
    /// deadlock, for example).
    ///
    /// Mutual attempts between mutiple tasks to lock overlapping ranges may
    /// result in a deadlock. To avoid this, have all tasks lock ranges in
    /// ascending or descending order consistently.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the slice.
    #[cfg(feature = "async")]
    pub async fn lock_async(
        &self,
        range: impl RangeBounds<usize>,
    ) -> RangeMutexGuard<'_, T> {
        // panics if out of range
        let range = util::range(self.data.as_ref().len(), range);
        std::future::poll_fn(move |ctx| {
            if range.is_empty() {
                return Poll::Ready(RangeMutexGuard::empty());
            }
            // Don't hold the mutex while waiting, only hold during the poll
            // call.
            let mut used = self.used.lock();
            match used
                .lock_range(&range, Some(|| Waiter::Task(ctx.waker().clone())))
            {
                Err(NotLocked) => Poll::Pending,
                Ok(Locked) => {
                    let data = &self.data.as_ref()[range.clone()];
                    let data = util::transpose_unsafecell_slice(data);
                    Poll::Ready(RangeMutexGuard {
                        data: NonNull::new(data.get()).unwrap(),
                        range: range.clone(),
                        used: Some(&self.used),
                        _variance: PhantomData,
                    })
                }
            }
        })
        .await
    }

    /// Returns the number of elements in the slice.
    pub fn len(&self) -> usize {
        self.data.as_ref().len()
    }
}

/// An RAII implementation of a “scoped lock” of a slice of a [`RangeMutex`].
/// When this structure is dropped (falls out of scope), the lock will be
/// unlocked.
///
/// The slice protected by the mutex can be accessed through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is created by the [`lock`][RangeMutex::lock] and
/// [`try_lock`][RangeMutex::try_lock] methods on [`RangeMutex`].
pub struct RangeMutexGuard<'l, T> {
    data: NonNull<[T]>,
    /// RangeMutexGuard<'l, T> should be covariant in 'l, but invariant in T.
    _variance: PhantomData<&'l mut [T]>,
    /// `range..is_empty()` if and only if `used.is_none()`
    range: Range<usize>,
    used: Option<&'l Mutex<RangesUsed>>,
}

unsafe impl<T: Send> Send for RangeMutexGuard<'_, T> {}
unsafe impl<T: Sync> Sync for RangeMutexGuard<'_, T> {}

impl<T> Default for RangeMutexGuard<'_, T> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<'l, T> RangeMutexGuard<'l, T> {
    /// A `RangeMutexGuard` pointing to an empty slice.
    pub fn empty() -> Self {
        Self {
            data: NonNull::<[T; 0]>::dangling(),
            range: 0..0,
            used: None,
            _variance: PhantomData,
        }
    }

    /// Divide this `RangeMutexGuard` into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)`, (excluding the index
    /// `mid` itself) and the second will contain all indices from `[mid, len)`
    /// (excluding the index `len` itself).
    ///
    /// # Panics
    ///
    /// Panics if `mid > len`.
    pub fn split_at(this: Self, mid: usize) -> (Self, Self) {
        assert!(mid <= this.len());
        if mid == 0 {
            return (Self::empty(), this);
        } else if mid == this.len() {
            return (this, Self::empty());
        }
        let this = ManuallyDrop::new(this);
        let mut used = this.used.as_ref().expect("this.len() > 0").lock();
        // SAFETY: `mid <= this.len()`, so `this.data.add(mid)` is defined.
        let (head_data, tail_data) =
            unsafe { util::split_slice_at(this.data, mid) };
        let (head, tail) = used.split_locked_range(&this.range, mid);
        (
            Self {
                data: head_data,
                range: head,
                used: this.used,
                _variance: PhantomData,
            },
            Self {
                data: tail_data,
                range: tail,
                used: this.used,
                _variance: PhantomData,
            },
        )
    }

    /// Reduce the extent of this `RangeMutexGuard` to a subrange. Elements
    /// outside of `self[range]` are unlocked, and a guard for `self[range]` is
    /// returned.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the slice.
    pub fn slice(this: Self, range: impl RangeBounds<usize>) -> Self {
        // TODO: make more efficient
        let range = util::range(this.len(), range);
        let (this, _tail) = Self::split_at(this, range.end);
        let (_head, this) = Self::split_at(this, range.start);
        this
    }
}

impl<T> Deref for RangeMutexGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: self.data is uniquely accessible to this RangeMutexGuard, so
        // it is sound to dereference it shared-ly from &self. (Or it is empty
        // and dangling and thus sound to dereference.)
        unsafe { self.data.as_ref() }
    }
}

impl<T> DerefMut for RangeMutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: self.data is uniquely accessible to this RangeMutexGuard, so
        // it is sound to dereference it mutably from &mut self. (Or it is empty
        // and dangling and thus sound to dereference.)
        unsafe { self.data.as_mut() }
    }
}

impl<'l, T> Drop for RangeMutexGuard<'l, T> {
    fn drop(&mut self) {
        if let Some(used) = self.used {
            let mut used = used.lock();
            used.unlock_range(&self.range);
        } else {
            // `range.is_empty()` if and only if `used.is_none()`
            debug_assert_eq!(self.range.len(), 0)
        }
    }
}

impl<T> AsRef<[T]> for RangeMutexGuard<'_, T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for RangeMutexGuard<'_, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}
