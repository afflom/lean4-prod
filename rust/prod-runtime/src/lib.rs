//! Host-side execution helpers for generated Lean code.
//!
//! The generated functions themselves remain synchronous, pure, allocation
//! free, and `no_std`. This crate is the optional host boundary for callers
//! that want to run independent calls concurrently. It deliberately owns the
//! thread creation and uses caller-owned input/output slices, so the portable
//! generated core does not need an executor or a threading dependency.
//!
//! [`parallel_map`] uses a bounded number of scoped workers. Each worker gets
//! one disjoint contiguous input/output chunk, and results are joined in chunk
//! order. Therefore output bytes do not depend on scheduling. The function is
//! blocking; async applications should call it from their runtime's blocking
//! pool (for example, Tokio's `spawn_blocking`).

use std::fmt;
use std::thread;

/// Failure from a bounded parallel map.
#[derive(Debug, PartialEq, Eq)]
pub enum ParallelError<E> {
    /// The caller supplied zero workers.
    InvalidWorkerCount,
    /// Input and output must describe the same number of elements.
    LengthMismatch { input: usize, output: usize },
    /// One worker returned its computation error.
    Worker(E),
    /// A worker panicked. The panic is contained at the host boundary.
    WorkerPanicked,
}

impl<E: fmt::Display> fmt::Display for ParallelError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWorkerCount => f.write_str("parallel worker count must be non-zero"),
            Self::LengthMismatch { input, output } => write!(
                f,
                "parallel input/output length mismatch: input={input}, output={output}"
            ),
            Self::Worker(error) => write!(f, "parallel worker failed: {error}"),
            Self::WorkerPanicked => f.write_str("parallel worker panicked"),
        }
    }
}

/// Apply `f` to every input/output pair using at most `workers` threads.
///
/// The output slice is split into disjoint chunks before any worker starts;
/// no worker can alias another worker's output. The actual worker count is
/// clamped to the input length, and chunks are contiguous and deterministic.
/// A worker error or panic is reported only after all workers have been joined.
/// If a worker fails, output contents are unspecified because other chunks may
/// already have completed.
///
/// This function is intentionally blocking and host-only. It is safe to call
/// with a generated pure function because the closure receives exclusive
/// access to each output element and shared access to each input element.
pub fn parallel_map<T, U, E, F>(
    input: &[T],
    output: &mut [U],
    workers: usize,
    f: F,
) -> Result<(), ParallelError<E>>
where
    T: Sync,
    U: Send,
    E: Send,
    F: Fn(&T, &mut U) -> Result<(), E> + Sync,
{
    if workers == 0 {
        return Err(ParallelError::InvalidWorkerCount);
    }
    if input.len() != output.len() {
        return Err(ParallelError::LengthMismatch {
            input: input.len(),
            output: output.len(),
        });
    }
    if input.is_empty() {
        return Ok(());
    }

    let worker_count = workers.min(input.len());
    let chunk_size = input.len().div_ceil(worker_count);

    if worker_count == 1 {
        for (value, slot) in input.iter().zip(output.iter_mut()) {
            f(value, slot).map_err(ParallelError::Worker)?;
        }
        return Ok(());
    }

    thread::scope(|scope| {
        let mut handles = Vec::with_capacity(worker_count);
        for (input_chunk, output_chunk) in
            input.chunks(chunk_size).zip(output.chunks_mut(chunk_size))
        {
            handles.push(scope.spawn(|| {
                for (value, slot) in input_chunk.iter().zip(output_chunk.iter_mut()) {
                    f(value, slot)?;
                }
                Ok::<(), E>(())
            }));
        }

        // Joining in spawn order makes error selection deterministic even if
        // workers finish in a different order. Every handle is joined before
        // returning so no background work survives this call.
        let mut failure = None;
        for handle in handles {
            match handle.join() {
                Ok(Ok(())) => {}
                Ok(Err(error)) => {
                    if failure.is_none() {
                        failure = Some(ParallelError::Worker(error));
                    }
                }
                Err(_) => {
                    if failure.is_none() {
                        failure = Some(ParallelError::WorkerPanicked);
                    }
                }
            }
        }
        failure.map_or(Ok(()), Err)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_into_disjoint_chunks_deterministically() {
        let input: Vec<u64> = (0..257).collect();
        let mut output = vec![0; input.len()];
        parallel_map(&input, &mut output, 7, |value, slot| {
            *slot = value * 3 + 1;
            Ok::<(), ()>(())
        })
        .unwrap();
        assert_eq!(
            output,
            input.iter().map(|value| value * 3 + 1).collect::<Vec<_>>()
        );
    }

    #[test]
    fn clamps_workers_and_handles_empty_input() {
        let input = [1, 2, 3];
        let mut output = [0; 3];
        parallel_map(&input, &mut output, 99, |value, slot| {
            *slot = *value;
            Ok::<(), ()>(())
        })
        .unwrap();
        assert_eq!(output, input);

        let mut empty: [u64; 0] = [];
        parallel_map(&[], &mut empty, 1, |_: &u64, _: &mut u64| Ok::<(), ()>(())).unwrap();
    }

    #[test]
    fn rejects_invalid_shapes() {
        let mut output = [0; 2];
        assert_eq!(
            parallel_map(&[1, 2], &mut output, 0, |_: &i32, _: &mut i32| {
                Ok::<(), ()>(())
            }),
            Err(ParallelError::InvalidWorkerCount)
        );
        let mut short = [0; 1];
        assert_eq!(
            parallel_map(&[1, 2], &mut short, 1, |_: &i32, _: &mut i32| {
                Ok::<(), ()>(())
            }),
            Err(ParallelError::LengthMismatch {
                input: 2,
                output: 1
            })
        );
    }

    #[test]
    fn joins_all_workers_before_returning_errors() {
        let input: Vec<u64> = (0..32).collect();
        let mut output = vec![0; input.len()];
        let result = parallel_map(&input, &mut output, 4, |value, slot| {
            if *value == 17 {
                Err("bad input")
            } else {
                *slot = *value;
                Ok(())
            }
        });
        assert_eq!(result, Err(ParallelError::Worker("bad input")));
    }

    #[test]
    fn contains_worker_panics_at_the_boundary() {
        let input = [1, 2, 3, 4];
        let mut output = [0; 4];
        let result = parallel_map(&input, &mut output, 2, |value, slot| {
            assert_ne!(*value, 3);
            *slot = *value;
            Ok::<(), ()>(())
        });
        assert_eq!(result, Err(ParallelError::WorkerPanicked));
    }
}
