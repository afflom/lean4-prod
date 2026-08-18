#![allow(non_snake_case)] // generated names mirror Lean definitions

//! Parallel calls against the actual Lean-exported functions.

use prod_core::{belt, digitCount, ComputeError, Instance};
use prod_runtime::{parallel_map, ParallelError};

prod_macros::prod_defs! { ir = "goldens.ir" }

const CANONICAL: Instance = Instance { q: 4, T: 3, O: 8 };
const DEMO_SMALL: Instance = Instance { q: 2, T: 2, O: 4 };
const THIRD: Instance = Instance { q: 5, T: 1, O: 3 };

#[test]
fn parallel_map_runs_generated_pure_functions_deterministically() -> Result<(), ComputeError> {
    let inputs = [0, 1, 7, 8, 43, 511];
    let expected: Vec<u64> = inputs
        .iter()
        .map(|n| digitCount(10, *n, CANONICAL))
        .collect::<Result<_, _>>()?;
    let mut output = [0; 6];

    parallel_map(&inputs, &mut output, 3, |n, slot| {
        *slot = digitCount(10, *n, CANONICAL)?;
        Ok::<(), ComputeError>(())
    })
    .map_err(|error| match error {
        ParallelError::Worker(error) => error,
        ParallelError::InvalidWorkerCount
        | ParallelError::LengthMismatch { .. }
        | ParallelError::WorkerPanicked => ComputeError::OutputTooSmall,
    })?;

    assert_eq!(output, expected.as_slice());
    Ok(())
}

#[test]
fn generated_errors_are_returned_in_input_chunk_order() {
    let inputs = [CANONICAL, DEMO_SMALL, Instance { q: 1, T: 1, O: 70 }, THIRD];
    let mut output = [0; 4];
    let result = parallel_map(&inputs, &mut output, 2, |instance, slot| {
        *slot = belt(*instance)?;
        Ok::<(), ComputeError>(())
    });

    assert_eq!(
        result,
        Err(ParallelError::Worker(ComputeError::PowOverflow))
    );
}
