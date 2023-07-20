mod range;
use std::{cell::UnsafeCell, mem::ManuallyDrop, ops::Range};

pub use range::range;

pub fn transpose_unsafecell_slice<'a, T>(
    slice: &'a [UnsafeCell<T>],
) -> &'a UnsafeCell<[T]> {
    // SAFETY: [UnsafeCell<T>] has the same in-memory representation as
    // UnsafeCell<[T]>.
    unsafe { &*(slice as *const [UnsafeCell<T>] as *const UnsafeCell<[T]>) }
}

/// Assumes r1 and r2 are nonempty.
pub fn overlaps(r1: &Range<usize>, r2: &Range<usize>) -> bool {
    r1.end > r2.start && r1.start < r2.end
}

pub fn wrap_unsafecell_array<T, const N: usize>(
    array: [T; N],
) -> [UnsafeCell<T>; N] {
    // SAFETY: An owned [T; N] can be interpreted as [UnsafeCell<T>; N],
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the ownership ensures that "adding" interior mutability is not an
    // issue.
    unsafe {
        let array = ManuallyDrop::new(array);
        std::mem::transmute_copy(&array)
    }
}

pub fn unwrap_unsafecell_array<T, const N: usize>(
    array: [UnsafeCell<T>; N],
) -> [T; N] {
    // SAFETY: A uniquely borrowed [UnsafeCell<T>; N] can be interpreted as [T;
    // N], since UnsafeCell<T> has the same in-memory representation as T,
    // and the ownership ensures that "removing" interior mutability is not an
    // issue.
    unsafe {
        let array = ManuallyDrop::new(array);
        std::mem::transmute_copy(&array)
    }
}

pub fn wrap_unsafecell_slice<'a, T>(
    slice: &'a mut [T],
) -> &'a mut [UnsafeCell<T>] {
    // SAFETY: A uniquely borrowed [T] can be interpreted as [UnsafeCell<T>],
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the unique borrow ensures that "adding" interior mutability is not an
    // issue.
    unsafe { &mut *(slice as *mut [T] as *mut [UnsafeCell<T>]) }
}

pub fn unwrap_unsafecell_slice<'a, T>(
    slice: &'a mut [UnsafeCell<T>],
) -> &'a mut [T] {
    // SAFETY: A uniquely borrowed [UnsafeCell<T>] can be interpreted as [T],
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the unique borrow ensures that "removing" interior mutability is not
    // an issue.
    unsafe { &mut *(slice as *mut [UnsafeCell<T>] as *mut [T]) }
}

pub fn wrap_unsafecell_vec<T>(vec: Vec<T>) -> Vec<UnsafeCell<T>> {
    // SAFETY: Owned `T`s can be interpreted as `UnsafeCell<T>`s,
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the ownership ensures that "adding" interior mutability is not an
    // issue.
    let mut vec = ManuallyDrop::new(vec);
    let length = vec.len();
    let capacity = vec.capacity();
    let ptr = vec.as_mut_ptr();
    unsafe { Vec::from_raw_parts(ptr.cast(), length, capacity) }
}

pub fn unwrap_unsafecell_vec<T>(vec: Vec<UnsafeCell<T>>) -> Vec<T> {
    // SAFETY: Owned `UnsafeCell<T>`s can be interpreted as `T`s,
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the ownership ensures that "removing" interior mutability is not an
    // issue.
    let mut vec = ManuallyDrop::new(vec);
    let length = vec.len();
    let capacity = vec.capacity();
    let ptr = vec.as_mut_ptr();
    unsafe { Vec::from_raw_parts(ptr.cast(), length, capacity) }
}
