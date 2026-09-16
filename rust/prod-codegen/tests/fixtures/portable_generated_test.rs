use core::cmp::Ordering;

#[test]
fn real_lexlean_portable_operations_execute_with_exact_rust_semantics() {
    assert_eq!(portable_expanded::checkedAddInt64(i64::MAX, 1), None);
    assert_eq!(portable_expanded::checkedAddInt64(40, 2), Some(42));
    assert_eq!(portable_expanded::checkedSubtractInt64(i64::MIN, 1), None);
    assert_eq!(portable_expanded::checkedMultiplyInt64(i64::MAX, 2), None);
    assert_eq!(portable_expanded::checkedNegateInt64(i64::MIN), None);
    assert_eq!(portable_expanded::checkedQuotientInt64(7, 0), None);
    assert_eq!(portable_expanded::checkedQuotientInt64(i64::MIN, -1), None);
    assert_eq!(portable_expanded::checkedQuotientInt64(-7, 2), Some(-3));

    assert_eq!(portable_expanded::andUInt64(12, 10), 8);
    assert_eq!(portable_expanded::orUInt64(12, 10), 14);
    assert_eq!(portable_expanded::xorUInt64(12, 10), 6);
    assert_eq!(portable_expanded::notUInt64(0), u64::MAX);
    assert_eq!(portable_expanded::shiftUInt64(1, 63), Some(1 << 63));
    assert_eq!(portable_expanded::shiftUInt64(1, 64), None);
    assert_eq!(portable_expanded::shiftRightUInt64(8, 3), Some(1));

    assert_eq!(portable_expanded::appendBytes(vec![1, 2], vec![3]), vec![1, 2, 3]);
    assert_eq!(portable_expanded::byteLength(vec![1, 2, 3]), 3);
    assert_eq!(portable_expanded::byteAt(vec![1, 2, 3], 1), Some(2));
    assert_eq!(portable_expanded::byteAt(vec![1], u64::MAX), None);
    assert_eq!(portable_expanded::sliceBytes(vec![1, 2, 3], 1, 2), Some(vec![2, 3]));
    assert_eq!(portable_expanded::sliceBytes(vec![1], 1, 1), None);
    assert_eq!(portable_expanded::compareByteStrings(vec![1], vec![2]), Ordering::Less);

    assert_eq!(portable_expanded::byteFixture(), vec![170, 187, 127, 255]);
    assert_eq!(portable_expanded::emptyByteFixture(), Vec::<u8>::new());
    assert_eq!(portable_expanded::nestedByteFixture(true, vec![0xc3, 0xa9]), vec![0, 128, 255, 0xc3, 0xa9]);
    assert_eq!(portable_expanded::nestedByteFixture(false, vec![1, 2, 3]), vec![255, 0]);
    assert!(portable_expanded::byteLiteralEquals(&[0, 128, 255]));
    assert!(!portable_expanded::byteLiteralEquals(&[]));
    assert!(!portable_expanded::byteLiteralEquals(&[0, 128, 254]));
    assert!(portable_expanded::emptyByteLiteralEquals());
    assert_eq!(portable_expanded::reuseByteFixture(vec![0xc3, 0xa9]), vec![0, 128, 255, 0xc3, 0xa9]);
    assert_eq!(portable_expanded::reuseByteFixture(vec![0xff]), vec![255, 0]);
    assert_eq!(portable_expanded::reuseByteFixture(vec![]), vec![0, 128, 255]);
    assert_eq!(portable_expanded::wrappedByteLength(vec![0, 128, 255]), 3);
    assert_eq!(portable_expanded::wrappedByteLength(vec![]), 0);
    for (left, right) in [
        (vec![], vec![]),
        (vec![], vec![0, 128, 255]),
        (vec![255, 128, 0], vec![]),
        (vec![255, 128, 0], vec![0, 128, 255]),
    ] {
        let mut expected = left.clone();
        expected.extend_from_slice(&right);
        assert_eq!(portable_expanded::wrappedAppendBytes(left, right), expected);
    }
    for value in [vec![], vec![0, 128, 255]] {
        let mut expected = value.clone();
        expected.extend_from_slice(&value);
        assert_eq!(portable_expanded::aliasedAppendBytes(value), expected);
    }
    for value in [vec![], vec![0xff], vec![b'a'; 65]] {
        assert_eq!(portable_expanded::boundedReuseByteFixture(value), vec![255, 0]);
    }
    for value in [vec![0xc3, 0xa9], vec![b'a'; 64]] {
        let mut expected = vec![0, 128, 255];
        expected.extend_from_slice(&value);
        assert_eq!(portable_expanded::boundedReuseByteFixture(value), expected);
    }

    let text = String::from("portable ✓");
    let encoded = portable_expanded::encodeUtf8(text.clone());
    assert_eq!(portable_expanded::decodeUtf8(encoded), Some(text));
    assert_eq!(portable_expanded::decodeUtf8(vec![0xff]), None);
    assert_eq!(portable_expanded::parseInt64(String::from("-42")), Some(-42));
    assert_eq!(portable_expanded::parseInt64(String::from("+42")), None);
    assert_eq!(portable_expanded::parseInt64(String::from("042")), None);
    assert_eq!(portable_expanded::formatInt64(i64::MIN), i64::MIN.to_string());
    assert_eq!(
        portable_expanded::splitBounded(String::from("a\tb"), String::from("\t"), 2),
        Some(vec![String::from("a"), String::from("b")])
    );
    assert_eq!(
        portable_expanded::splitBounded(String::from("a\tb"), String::from("\t"), 1),
        None
    );
    assert_eq!(
        portable_expanded::joinStrings(&[String::from("a"), String::from("b")], String::from("\t")),
        String::from("a\tb")
    );
}
