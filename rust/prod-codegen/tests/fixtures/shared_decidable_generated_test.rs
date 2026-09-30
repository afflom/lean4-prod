use shared_decidable::*;

#[test]
fn repeated_conditions_preserve_every_record_field() {
    for (flag, expected) in [(false, [2, 4, 6]), (true, [1, 3, 5])] {
        let result = choose(flag);
        assert_eq!([result.first, result.second, result.third], expected);
    }
    for phase in [0, 1, 2, 3, 4, 255, 65535, u32::MAX as u64, u64::MAX] {
        let result = choosePhase(phase);
        assert_eq!(
            [result.first, result.second, result.third],
            if phase == 3 { [1, 3, 5] } else { [2, 4, 6] },
            "phase {phase}"
        );
    }
}

#[test]
fn actual_byte_dispatch_exercises_both_shared_branches() {
    for length in 0..=128 {
        for byte in [0, 1, 127, 255] {
            let result = entry(vec![byte; length]);
            assert_eq!(result, if length == 3 { [1, 3, 5] } else { [2, 4, 6] });
        }
    }
}
