#![allow(non_snake_case)] // generated code mirrors Lean definition names

//! Certification that the generated code performs zero heap activity.
//!
//! `prod-core` has no `extern crate alloc`, so an allocating *type* could not
//! compile — but that says nothing about allocations hidden inside a call.
//! This test installs a counting global allocator and asserts the counter does
//! not move across the generated functions, including the list builder that
//! writes into a caller-owned buffer.
//!
//! Must run serially (`just no-alloc` passes `--test-threads=1`): the counter
//! is process-global.

use prod_alloc_counter::{activity, CountingAllocator};
use prod_core::{
    belt, classDecode, classIndex, class_count, digitCount, digitSum, digits, sameClass,
    smallEnough, stride, tryClassDecode, ComputeError, Instance,
};

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

// `Instance` carries an invariant, so its fields are `pub(crate)` and this is
// an integration test — external to the crate. This was a `const`; a `const`
// cannot call a fallible constructor, so it is built inside the test with `?`.

/// Run `body`, and fail if it caused any heap activity.
///
/// The closure is `#[inline(never)]`-free on purpose: whatever the optimiser
/// does, an allocation would still pass through the global allocator.
fn assert_no_allocation<T>(what: &str, body: impl FnOnce() -> T) -> T {
    let before = activity();
    let value = body();
    let after = activity();
    assert_eq!(
        after,
        before,
        "{what} performed {} heap operation(s); generated code must be allocation-free",
        after - before
    );
    value
}

/// One test, not several: the counter is process-global, so a sibling test
/// running concurrently would perturb it. Keeping the whole certification in a
/// single function makes it correct under any `--test-threads` setting.
#[test]
fn generated_definitions_never_touch_the_heap() -> Result<(), ComputeError> {
    // Guard against the certification passing vacuously: a mis-wired
    // `#[global_allocator]` would make every count zero.
    let before = activity();
    let boxed = Box::new(7u64);
    assert_eq!(*boxed, 7);
    drop(boxed);
    assert!(
        activity() > before,
        "the counting allocator is not installed; the no-alloc assertions prove nothing"
    );

    // Built outside every `assert_no_allocation` region below, so the
    // measurements cover the generated definitions and not the constructor.
    let canonical = Instance::new(4, 3, 8)?;

    // The checked constructor itself, on both paths: the invariant check is
    // plain comparisons, and `InvariantViolated` carries a `&'static str`, so
    // neither accepting nor rejecting can touch the heap.
    assert_no_allocation("Instance::new (accepted)", || Instance::new(4, 3, 8))?;
    assert_eq!(
        assert_no_allocation("Instance::new (rejected)", || Instance::new(0, 3, 8)),
        Err(ComputeError::InvariantViolated("UorAtlas.Instance"))
    );

    // Scalar definitions.
    assert_eq!(assert_no_allocation("stride", || stride(canonical))?, 24);
    assert_eq!(
        assert_no_allocation("class_count", || class_count(canonical))?,
        96
    );
    assert_eq!(assert_no_allocation("belt", || belt(canonical))?, 12_288);
    assert_eq!(
        assert_no_allocation("classIndex", || classIndex(1, 2, 3, canonical))?,
        43
    );
    assert_eq!(
        assert_no_allocation("classDecode", || classDecode(43, canonical))?,
        (1, (2, 3))
    );

    // Recursion, guards, and `Option`.
    assert_eq!(
        assert_no_allocation("digitCount", || digitCount(10, 43, canonical))?,
        2
    );
    assert!(assert_no_allocation("sameClass", || sameClass(
        43, 44, canonical
    ))?);
    assert!(assert_no_allocation("smallEnough", || smallEnough(
        100, canonical
    ))?);
    assert_eq!(
        assert_no_allocation("tryClassDecode", || tryClassDecode(43, canonical))?,
        Some((1, (2, 3)))
    );

    // The list path: a caller-owned buffer in, a borrowed slice back out.
    // This is the case that used to allocate a `Box`-linked list per cons.
    let mut buffer = [0u64; 64];
    let len = assert_no_allocation("digits", || digits(10, 43, canonical, &mut buffer))?;
    assert_eq!(&buffer[..len], &[3, 5]);
    assert_eq!(
        assert_no_allocation("digitSum", || digitSum(&buffer[..len]))?,
        8
    );

    // Error construction and propagation must be allocation-free too — an
    // error path that allocates is still an allocation on hostile input.
    // `1, 1, 70` satisfies the invariant, so `new` accepts it; it is `belt`'s
    // power that overflows.
    let overflowing = Instance::new(1, 1, 70)?;
    assert_eq!(
        assert_no_allocation("belt overflow", || belt(overflowing)),
        Err(ComputeError::PowOverflow)
    );
    let mut too_small = [0u64; 1];
    assert_eq!(
        assert_no_allocation("digits into an undersized buffer", || digits(
            10,
            43,
            canonical,
            &mut too_small
        )),
        Err(ComputeError::OutputTooSmall)
    );

    Ok(())
}
