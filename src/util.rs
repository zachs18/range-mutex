mod range;
use std::{cell::UnsafeCell, ops::Range};

pub use range::range;

pub fn transpose_unsafecell_slice<'a, T>(slice: &'a [UnsafeCell<T>]) -> &'a UnsafeCell<[T]> {
    // SAFETY: [UnsafeCell<T>] has the same in-memory representation as UnsafeCell<[T]>.
    unsafe { &*(slice as *const [UnsafeCell<T>] as *const UnsafeCell<[T]>) }
}

pub fn wrap_unsafecell_slice<'a, T>(slice: &'a mut [T]) -> &'a mut [UnsafeCell<T>] {
    // SAFETY: A uniquely borrowed [T] can be interpreted as [UnsafeCell<T>],
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the unique borrow ensures that "adding" interior mutability is not an issue.
    unsafe { &mut *(slice as *mut [T] as *mut [UnsafeCell<T>]) }
}

pub fn unwrap_unsafecell_slice<'a, T>(slice: &'a mut [UnsafeCell<T>]) -> &'a mut [T] {
    // SAFETY: A uniquely borrowed [UnsafeCell<T>] can be interpreted as [T],
    // since UnsafeCell<T> has the same in-memory representation as T.
    unsafe { &mut *(slice as *mut [UnsafeCell<T>] as *mut [T]) }
}

/// Assumes r1 and r2 are nonempty.
pub fn overlaps(r1: &Range<usize>, r2: &Range<usize>) -> bool {
    r1.end > r2.start && r1.start < r2.end
}

pub fn wrap_unsafecell_vec<T>(vec: Vec<T>) -> Vec<UnsafeCell<T>> {
    // SAFETY: A uniquely borrowed [T] can be interpreted as [UnsafeCell<T>],
    // since UnsafeCell<T> has the same in-memory representation as T,
    // and the unique borrow ensures that "adding" interior mutability is not an issue.
    // unsafe { &mut *(slice as *mut [T] as *mut [UnsafeCell<T>]) }
    todo!()
}

pub fn unwrap_unsafecell_vec<T>(vec: Vec<UnsafeCell<T>>) -> Vec<T> {
    // SAFETY: A uniquely borrowed [UnsafeCell<T>] can be interpreted as [T],
    // since UnsafeCell<T> has the same in-memory representation as T.
    // unsafe { &mut *(slice as *mut [UnsafeCell<T>] as *mut [T]) }
    todo!()
}
