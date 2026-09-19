#[test]
fn imported_index_matches_slice_access_for_all_octets_and_boundaries() {
    for size in [0_usize, 1, 2, 3, 4, 16, 63, 64] {
        for octet in 0..=255_u8 {
            let bytes = (0..size)
                .map(|position| octet.wrapping_add(position as u8))
                .collect::<Vec<_>>();
            for position in 0..=size + 1 {
                assert_eq!(
                    byte_index_fixture::read(bytes.clone(), position as u64),
                    bytes.get(position).copied()
                );
            }
            assert_eq!(byte_index_fixture::read(bytes.clone(), u64::MAX), None);
            let expected = match bytes.get(3) {
                None => 255,
                Some(128) => 1,
                Some(_) => 0,
            };
            assert_eq!(byte_index_fixture::entry(bytes), vec![expected]);
        }
    }
}
