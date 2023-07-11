use std::{
    cell::UnsafeCell,
    cmp::Ordering,
    ops::{Deref, DerefMut, Range, RangeBounds},
    ptr::NonNull,
    sync::Mutex,
    thread::Thread,
};

#[cfg(test)]
mod tests;
mod util;

#[derive(Default)]
struct RangesUsed {
    ranges: Vec<Range<usize>>,
    waiting: Vec<(Thread, Range<usize>)>,
}

impl RangesUsed {
    const fn new() -> Self {
        Self {
            ranges: Vec::new(),
            waiting: Vec::new(),
        }
    }

    fn overlapping_range_idx(&self, range: &Range<usize>) -> Result<usize, usize> {
        debug_assert!(range.len() > 0, "empty ranges should be handled already");
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

    fn lock_range(
        &mut self,
        range: &Range<usize>,
        add_waiter_if_not_locked: bool,
    ) -> Result<(), ()> {
        let idx = self.overlapping_range_idx(&range);
        match idx {
            Ok(_overlapping_range_idx) => {
                if add_waiter_if_not_locked {
                    self.waiting.push((std::thread::current(), range.clone()));
                }
                Err(())
            }
            Err(insert_idx) => {
                self.ranges.insert(insert_idx, range.clone());
                Ok(())
            }
        }
    }

    pub fn unlock_range(&mut self, range: &Range<usize>) {
        let idx = self.overlapping_range_idx(&range).expect("range is locked");
        debug_assert_eq!(&self.ranges[idx], range);
        self.ranges.remove(idx);
        self.waiting.retain(|(thread, waiting_range)| {
            // TODO: more precise unpark selection
            // e.g. don't unpark two overlapping waiters,
            // don't unpark a waiter that overlaps with another existing lock.
            let should_unpark_and_remove = util::overlaps(range, waiting_range);
            if should_unpark_and_remove {
                thread.unpark();
            }
            // return value is should *not* remove
            !should_unpark_and_remove
        })
    }
}

pub unsafe trait RangeMutexBackingStorage<T>: AsMut<[T]> {
    type AsUnsafeCell: AsMut<[UnsafeCell<T>]>;
    fn into_unsafecell(self) -> Self::AsUnsafeCell;
    fn from_unsafecell(value: Self::AsUnsafeCell) -> Self;
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

pub struct RangeMutex<'a, T> {
    data: &'a mut [UnsafeCell<T>],
    used: Mutex<RangesUsed>,
}

unsafe impl<T: Send> Sync for RangeMutex<'_, T> {}
unsafe impl<T: Send> Send for RangeMutex<'_, T> {}

impl<'a, T> RangeMutex<'a, T> {
    pub fn new(values: &'a mut [T]) -> Self {
        let data = util::wrap_unsafecell_slice(values);

        Self {
            data,
            used: Mutex::new(RangesUsed::new()),
        }
    }

    pub fn get_mut(&mut self) -> &mut [T] {
        util::unwrap_unsafecell_slice(&mut self.data)
    }

    pub fn undo_leak(&mut self) -> &mut [T] {
        let used = self.used.get_mut().unwrap();
        used.ranges.clear();
        used.waiting.clear();
        self.get_mut()
    }

    pub fn try_lock(&self, range: impl RangeBounds<usize>) -> Option<RangeMutexGuard<'_, T>> {
        // panics if out of range
        let range = util::range(self.data.len(), range);
        if range.len() == 0 {
            return Some(RangeMutexGuard {
                data: NonNull::<[T; 0]>::dangling(),
                range,
                lock: &self.used,
            });
        }
        let mut used = self.used.lock().unwrap();

        match used.lock_range(&range, false) {
            Err(_not_locked) => None,
            Ok(_locked) => {
                let data = &self.data[range.clone()];
                let data = util::transpose_unsafecell_slice(data);
                Some(RangeMutexGuard {
                    data: NonNull::new(data.get()).unwrap(),
                    range,
                    lock: &self.used,
                })
            }
        }
    }

    pub fn lock(&self, range: impl RangeBounds<usize>) -> RangeMutexGuard<'_, T> {
        // panics if out of range
        let range = util::range(self.data.len(), range);
        if range.len() == 0 {
            return RangeMutexGuard {
                data: NonNull::<[T; 0]>::dangling(),
                range,
                lock: &self.used,
            };
        }
        let mut used = Some(self.used.lock().unwrap());
        loop {
            match used.as_mut().unwrap().lock_range(&range, true) {
                Err(_not_locked) => {
                    drop(used.take());
                    std::thread::park();
                    used = Some(self.used.lock().unwrap());
                }
                Ok(_locked) => {
                    let data = &self.data[range.clone()];
                    let data = util::transpose_unsafecell_slice(data);
                    return RangeMutexGuard {
                        data: NonNull::new(data.get()).unwrap(),
                        range,
                        lock: &self.used,
                    };
                }
            }
        }
    }
}

pub struct RangeMutexGuard<'l, T> {
    data: NonNull<[T]>,
    range: Range<usize>,
    lock: &'l Mutex<RangesUsed>,
}

impl<T> Deref for RangeMutexGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { self.data.as_ref() }
    }
}

impl<T> DerefMut for RangeMutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.data.as_mut() }
    }
}

impl<'l, T> Drop for RangeMutexGuard<'l, T> {
    fn drop(&mut self) {
        if self.range.len() == 0 {
            // Nothing to unlock
            return;
        }
        let mut used = self.lock.lock().unwrap();
        used.unlock_range(&self.range);
    }
}
