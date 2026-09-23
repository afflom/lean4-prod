use byte_index_fixture::{readSlice, sliceEntry};

#[test]
fn imported_slices_preserve_bounds_counts_and_overflow_rejection() {
    for size in [0_usize, 1, 2, 3, 4, 16, 63, 64] {
        for octet in 0..=255_u8 {
            let bytes = (0..size)
                .map(|position| octet.wrapping_add(position as u8))
                .collect::<Vec<_>>();
            for start in 0..=size + 1 {
                for count in 0..=size + 1 {
                    assert_eq!(
                        readSlice(bytes.clone(), start as u64, count as u64),
                        bytes.get(start..start + count).map(<[u8]>::to_vec)
                    );
                }
            }
            for (start, count) in [(u64::MAX, 0), (u64::MAX, 1), (1, u64::MAX), (0, u64::MAX)] {
                assert_eq!(readSlice(bytes.clone(), start, count), None);
            }
            assert_eq!(
                sliceEntry(bytes.clone()),
                bytes.get(1..3).map_or_else(|| vec![255], <[u8]>::to_vec)
            );
        }
    }
}
