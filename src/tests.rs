use std::{sync::atomic::AtomicBool, time::Duration};

use crate::RangeMutex;

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
