use owned_accumulator_fixture::{collect, entry, Input};

#[test]
fn exact_chunk_order_and_complete_64_mib_domain_boundary() {
    const CHUNK: usize = 262144;
    for count in [0, 1, 2, 3, 16, 256] {
        let mut input = vec![0; count * CHUNK];
        for (index, chunk) in input.chunks_mut(CHUNK).enumerate() {
            chunk.fill(index as u8);
            chunk[0] = (index ^ 0x55) as u8;
        }
        let expected: Vec<u8> = input.chunks(CHUNK).rev().flatten().copied().collect();
        assert_eq!(entry(input.clone()), Ok(expected.clone()), "{count} chunks");
        assert_eq!(entry(input), Ok(expected), "repeat {count} chunks");
    }
    for size in [1, 255, CHUNK - 1, CHUNK + 1, 67108863, 67108865] {
        assert_eq!(entry(vec![0; size]), Ok(vec![255]), "malformed size {size}");
    }
    assert_eq!(collect(&Input {bytes: vec![]}, &[], 0).unwrap().items.len(), 0);
    assert_eq!(collect(&Input {bytes: vec![]}, &[], 1).unwrap().items.len(), 0);
}
