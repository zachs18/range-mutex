use std::{ops::Bound, sync::atomic::AtomicBool, time::Duration};

use itertools::Itertools;

use crate::{RangeMutex, RangeMutexGuard};

#[test]
fn basic() {
    let mut data = vec![0u8; 300];
    let mut mutex = RangeMutex::new(&mut data[..]);
    {
        let mut g1 = mutex.try_lock(..100).unwrap();
        let mut g2 = mutex.try_lock(100..200).unwrap();
        let mut g3 = mutex
            .try_lock(40..40)
            .expect("empty range does not overlap with any other range");
        let mut g4 = mutex
            .try_lock(40..40)
            .expect("empty range does not overlap with any other range");
        assert!(mutex.try_lock(99..100).is_none(), "overlaps with g1");
        assert!(mutex.try_lock(100..101).is_none(), "overlaps with g2");
        assert!(mutex.try_lock(99..101).is_none(), "overlaps with g1 and g2");
        g1.fill(1);
        g2.fill(2);
        g3.fill(3);
        g4.fill(4);
        drop(g2);
        assert!(mutex.try_lock(99..100).is_none(), "overlaps with g1");
        assert!(mutex.try_lock(99..101).is_none(), "overlaps with g1");
        assert!(mutex.try_lock(100..101).is_some());
    }
    assert!(mutex.get_mut()[..100].iter().all(|&x| x == 1));
    assert!(mutex.get_mut()[100..200].iter().all(|&x| x == 2));
    assert!(mutex.get_mut()[200..].iter().all(|&x| x == 0));
    assert!(data[..100].iter().all(|&x| x == 1));
    assert!(data[100..200].iter().all(|&x| x == 2));
    assert!(data[200..].iter().all(|&x| x == 0));
}

#[test]
fn basic_park() {
    let mut data = vec![0u8; 300];
    let mut mutex = RangeMutex::new(&mut data[..]);
    // not perfect but meh
    let has_main_dropped_g1: AtomicBool = AtomicBool::new(false);
    let has_main_dropped_g2: AtomicBool = AtomicBool::new(false);
    std::thread::scope(|scope| {
        let mut g1 = mutex.try_lock(..100).unwrap();
        let mut g2 = mutex.try_lock(100..200).unwrap();
        let mut g3 = mutex
            .try_lock(40..40)
            .expect("empty range does not overlap with any other range");
        let mut g4 = mutex
            .try_lock(40..40)
            .expect("empty range does not overlap with any other range");
        scope.spawn(|| {
            let g5 = mutex.lock(99..100);
            assert!(
                has_main_dropped_g1.load(std::sync::atomic::Ordering::Acquire),
                "overlaps with g1"
            );
            assert_eq!(&*g5, [1]);
        });
        scope.spawn(|| {
            let g6 = mutex.lock(100..101);
            assert!(
                has_main_dropped_g2.load(std::sync::atomic::Ordering::Acquire),
                "overlaps with g2"
            );
            assert_eq!(&*g6, [2]);
        });
        scope.spawn(|| {
            let g7 = mutex.lock(99..101);
            assert!(
                has_main_dropped_g1.load(std::sync::atomic::Ordering::Acquire)
                    && has_main_dropped_g2
                        .load(std::sync::atomic::Ordering::Acquire),
                "overlaps with g1 and g2"
            );
            assert_eq!(&*g7, [1, 2]);
        });
        g1.fill(1);
        g2.fill(2);
        g3.fill(3);
        g4.fill(4);
        has_main_dropped_g2.store(true, std::sync::atomic::Ordering::Release);
        drop(g2);
        std::thread::sleep(Duration::from_millis(10));
        has_main_dropped_g1.store(true, std::sync::atomic::Ordering::Release);
        drop(g1);
        std::thread::sleep(Duration::from_millis(10));
    });
    assert!(mutex.get_mut()[..100].iter().all(|&x| x == 1));
    assert!(mutex.get_mut()[100..200].iter().all(|&x| x == 2));
    assert!(mutex.get_mut()[200..].iter().all(|&x| x == 0));
    assert!(data[..100].iter().all(|&x| x == 1));
    assert!(data[100..200].iter().all(|&x| x == 2));
    assert!(data[200..].iter().all(|&x| x == 0));
}

#[test]
fn empty() {
    let data = RangeMutex::new(vec![0_i32; 4]);
    let g1 = data.try_lock(0..0).unwrap();
    let g2 = data.try_lock(0..0).unwrap();
    assert_eq!(g1.len(), 0);
    assert_eq!(g2.len(), 0);
    let (g3, g4) = RangeMutexGuard::split_at(g1, 0);
    assert_eq!(g3.len(), 0);
    assert_eq!(g4.len(), 0);
    let g5 = data.try_lock(4..4).unwrap();
    assert_eq!(g5.len(), 0);
    let g6 = RangeMutexGuard::<i32>::default();
    let g7 = RangeMutexGuard::<i32>::empty();
    assert_eq!(g6.len(), 0);
    assert_eq!(g7.len(), 0);
}

#[test]
fn disjoint_time_overlapping_ranges() {
    let data = RangeMutex::new(vec![0; 128]);
    for i in 0..data.len() {
        data.lock(i..).fill(i);
    }
    itertools::assert_equal(data.into_inner(), 0..128);
}

#[test]
fn overlapping() {
    // Run multiple times for different index orders.
    for indices in [0, 1, 2, 3].into_iter().permutations(4) {
        let mut data = RangeMutex::new(vec![usize::MAX; 5]);
        std::thread::scope(|scope| {
            let data = &data;
            for i in indices {
                scope.spawn(move || {
                    let mut g = data.lock(i..=i + 1);
                    std::thread::sleep(Duration::from_millis(50));
                    g.fill(i);
                });
            }
        });

        // Possible orders:
        // * 0/2, 1/3: [0, 1, 1, 3, 3] (2 seconds)
        // * 1/3, 0/2: [0, 0, 2, 2, 3] (2 seconds)
        // * 0/3, 1, 2: [0, 1, 2, 2, 3] (3 seconds)
        // * 0/3, 2, 1: [0, 1, 1, 2, 3] (3 seconds)

        let data = data.get_mut();
        // Possible orders:
        // * 0/2, 1/3: [0, 1, 1, 3, 3]
        // * 1/3, 0/2: [0, 0, 2, 2, 3]
        // * 0/3, 1, 2: [0, 1, 2, 2, 3]
        // * 0/3, 2, 1: [0, 1, 1, 2, 3]
        assert!(
            data == [0, 1, 1, 3, 3]
                || data == [0, 0, 2, 2, 3]
                || data == [0, 1, 2, 2, 3]
                || data == [0, 1, 1, 2, 3]
        );
    }
}

#[test]
#[ignore = "takes up to 40 seconds"]
fn overlapping_with_sleep() {
    // Run multiple times for different index orders.
    for indices in [0, 1, 2, 3].into_iter().permutations(4) {
        let start = std::time::Instant::now();
        let mut data = RangeMutex::new(vec![usize::MAX; 5]);
        std::thread::scope(|scope| {
            let data = &data;
            for i in indices {
                scope.spawn(move || {
                    let mut g = data.lock(i..=i + 1);
                    std::thread::sleep(Duration::from_secs(1));
                    g.fill(i);
                });
            }
        });

        // Possible orders:
        // * 0/2, 1/3: [0, 1, 1, 3, 3] (2 seconds)
        // * 1/3, 0/2: [0, 0, 2, 2, 3] (2 seconds)
        // * 0/3, 1, 2: [0, 1, 2, 2, 3] (3 seconds)
        // * 0/3, 2, 1: [0, 1, 1, 2, 3] (3 seconds)

        let took = start.elapsed();
        let data = data.get_mut();
        // Possible orders:
        // * 0/2, 1/3: [0, 1, 1, 3, 3]
        // * 1/3, 0/2: [0, 0, 2, 2, 3]
        // * 0/3, 1, 2: [0, 1, 2, 2, 3]
        // * 0/3, 2, 1: [0, 1, 1, 2, 3]
        let seconds = Duration::from_secs;
        assert!(
            data == [0, 1, 1, 3, 3] && (seconds(2)..seconds(3)).contains(&took)
                || data == [0, 0, 2, 2, 3]
                    && (seconds(2)..seconds(3)).contains(&took)
                || data == [0, 1, 2, 2, 3]
                    && (seconds(3)..seconds(4)).contains(&took)
                || data == [0, 1, 1, 2, 3]
                    && (seconds(3)..seconds(4)).contains(&took)
        );
    }
}

#[test]
fn split() {
    let mut values = [0u8; 64];
    let mutex = RangeMutex::new(&mut values);

    let guard = mutex.try_lock(..).unwrap();
    assert_eq!(guard.len(), 64);
    let (g1, g2) = RangeMutexGuard::split_at(guard, 42);
    assert_eq!(g1.len(), 42);
    assert_eq!(g2.len(), 64 - 42);
    drop((g1, g2));

    let guard = mutex.try_lock(..).unwrap();
    assert_eq!(guard.len(), 64);
    let (g1, g2) = RangeMutexGuard::split_at(guard, 64);
    assert_eq!(g1.len(), 64);
    assert_eq!(g2.len(), 0);
    drop((g1, g2));

    let guard = mutex.try_lock(..).unwrap();
    assert_eq!(guard.len(), 64);
    let (g1, g2) = RangeMutexGuard::split_at(guard, 0);
    assert_eq!(g1.len(), 0);
    assert_eq!(g2.len(), 64);
    drop((g1, g2));
}

#[test]
fn slice() {
    let mut values = [0u8; 64];
    let mutex = RangeMutex::new(&mut values);

    let guard = mutex.try_lock(..).unwrap();
    assert_eq!(guard.len(), 64);
    let guard = RangeMutexGuard::slice(guard, 12..42);
    assert_eq!(guard.len(), 42 - 12);
    assert!(mutex.try_lock(..12).is_some());
    assert!(mutex.try_lock(42..).is_some());
}

#[cfg(feature = "async")]
#[tokio::test(start_paused = true)]
async fn async_lock() {
    use rand::seq::SliceRandom;
    use std::sync::Arc;
    // Run multiple times for different index orders.
    for indices in [0, 1, 2, 3].into_iter().permutations(4) {
        let start = tokio::time::Instant::now();
        let mut data = Arc::new(RangeMutex::new(vec![usize::MAX; 5]));
        let mut handles = vec![];
        for i in indices {
            let handle = tokio::spawn({
                let data = data.clone();
                async move {
                    let mut g = data.lock_async(i..=i + 1).await;
                    tokio::time::sleep(Duration::from_secs(1)).await;
                    g.fill(i);
                }
            });
            handles.push(handle);
        }
        handles.shuffle(&mut rand::thread_rng());
        for handle in handles {
            handle.await.unwrap();
        }

        // Possible orders:
        // * 0/2, 1/3: [0, 1, 1, 3, 3] (2 seconds)
        // * 1/3, 0/2: [0, 0, 2, 2, 3] (2 seconds)
        // * 0/3, 1, 2: [0, 1, 2, 2, 3] (3 seconds)
        // * 0/3, 2, 1: [0, 1, 1, 2, 3] (3 seconds)

        let took = start.elapsed();
        let data =
            Arc::get_mut(&mut data).expect("all tasks completed").get_mut();
        // Possible orders:
        // * 0/2, 1/3: [0, 1, 1, 3, 3]
        // * 1/3, 0/2: [0, 0, 2, 2, 3]
        // * 0/3, 1, 2: [0, 1, 2, 2, 3]
        // * 0/3, 2, 1: [0, 1, 1, 2, 3]
        assert!(
            data == [0, 1, 1, 3, 3] && took == Duration::from_secs(2)
                || data == [0, 0, 2, 2, 3] && took == Duration::from_secs(2)
                || data == [0, 1, 2, 2, 3] && took == Duration::from_secs(3)
                || data == [0, 1, 1, 2, 3] && took == Duration::from_secs(3)
        );
    }
}

/// ```rust,compile_fail,E0597
/// use range_mutex::RangeMutex;
/// let data: RangeMutex<&'static str, Vec<&'static str>> =
///     RangeMutex::new(vec!["Hello, world!"]);
/// {
///     let s = String::from("Oh, no!");
///     let mut g = data.lock(..);
///     // s does not live long enough
///     g[0] = &s;
/// }
/// dbg!(data.into_inner());
/// ```
#[allow(dead_code)]
pub struct AssertVarianceIsCorrect;

#[test]
#[should_panic]
fn ridiculous_range_1() {
    let mut values = [(); usize::MAX];
    let range_mutex = RangeMutex::new(&mut values);

    let _ = range_mutex.lock(..=usize::MAX);
}

#[test]
#[should_panic]
fn ridiculous_range_2() {
    let mut values = [(); usize::MAX];
    let range_mutex = RangeMutex::new(&mut values);

    let _ = range_mutex.lock((Bound::Excluded(usize::MAX), Bound::Unbounded));
}

#[test]
#[should_panic]
fn out_of_range_1() {
    let range_mutex = RangeMutex::new(&mut [(); 0]);

    let _ = range_mutex.lock(..1);
}

#[test]
#[should_panic]
fn out_of_range_2() {
    let mut values = [0u8; 4];
    let range_mutex = RangeMutex::new(&mut values);

    let _ = range_mutex.lock(2..1);
}

#[test]
fn into_inner_coverage() {
    // Array
    let range_mutex = RangeMutex::new([0u8; 42]);
    range_mutex.lock(..).fill(42);
    assert_eq!(range_mutex.into_inner(), [42; 42]);

    // &mut Array
    let mut values = [0u8; 42];
    let range_mutex = RangeMutex::new(&mut values);
    range_mutex.lock(..).fill(42);
    assert_eq!(range_mutex.into_inner(), &mut [42; 42]);

    // &mut Slice
    let mut values = [0u8; 42];
    let range_mutex = RangeMutex::new(&mut values[..]);
    range_mutex.lock(..).fill(42);
    assert_eq!(range_mutex.into_inner(), &mut [42; 42]);

    // Vec
    let range_mutex = RangeMutex::new(vec![0u8; 42]);
    range_mutex.lock(..).fill(42);
    assert_eq!(range_mutex.into_inner(), [42; 42]);

    // Boxed slice
    let range_mutex = RangeMutex::new(vec![0u8; 42].into_boxed_slice());
    range_mutex.lock(..).fill(42);
    assert_eq!(*range_mutex.into_inner(), [42; 42]);

    // RangeMutexGuard
    let range_mutex = RangeMutex::new(vec![0u8; 42].into_boxed_slice());
    {
        let range_mutex = RangeMutex::new(range_mutex.lock(..));
        range_mutex.lock(..).fill(42);
        assert_eq!(*range_mutex.into_inner(), [42; 42]);
    }
    assert_eq!(*range_mutex.into_inner(), [42; 42]);
}

#[test]
fn leak() {
    let mut values = [0; 64];
    let mut range_mutex = RangeMutex::new(&mut values);
    let mut g1 = range_mutex.lock(..32);
    g1.fill(42);
    std::mem::forget(g1);
    assert!(range_mutex.try_lock(..).is_none());
    assert!(range_mutex.try_lock(32..).is_some());
    assert_eq!(range_mutex.get_mut()[..32], [42; 32]);
    assert_eq!(range_mutex.get_mut()[32..], [0; 32]);
    assert!(range_mutex.try_lock(..).is_none());
    assert!(range_mutex.try_lock(32..).is_some());
    range_mutex.undo_leak();
    assert!(range_mutex.try_lock(..).is_some());
    assert!(range_mutex.try_lock(32..).is_some());
}

#[test]
fn zero_length() {
    let mut values = [0; 64];
    let range_mutex = RangeMutex::new(&mut values);
    let _g1 = range_mutex.lock(..32);
    assert_eq!(range_mutex.try_lock(..0).unwrap().len(), 0);
    assert_eq!(range_mutex.lock(..0).len(), 0);
    assert_eq!(range_mutex.try_lock(10..10).unwrap().len(), 0);
    assert_eq!(range_mutex.lock(10..10).len(), 0);
}

#[cfg(feature = "async")]
#[tokio::test(start_paused = true)]
async fn async_zero_length() {
    let mut values = [0; 64];
    let range_mutex = RangeMutex::new(&mut values);
    let _g1 = range_mutex.lock_async(..32).await;
    assert_eq!(range_mutex.try_lock(..0).unwrap().len(), 0);
    assert_eq!(range_mutex.lock_async(..0).await.len(), 0);
    assert_eq!(range_mutex.try_lock(10..10).unwrap().len(), 0);
    assert_eq!(range_mutex.lock_async(10..10).await.len(), 0);
}

#[test]
fn as_ref() {
    let mut values = [0; 64];
    let range_mutex = RangeMutex::new(&mut values);
    let mut guard = range_mutex.lock(..);
    guard.fill(42);
    assert_eq!(guard.as_ref(), &[42; 64]);
    assert_eq!(guard.as_mut(), &mut [42; 64]);
}
