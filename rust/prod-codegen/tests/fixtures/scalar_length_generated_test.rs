use scalar_length_fixture::{byteLength, entry, nestedLength, scalarLength, Text};

#[test]
fn every_unicode_scalar_has_length_one_not_its_utf8_width() {
    let mut checked = 0;
    for codepoint in 0..=0x10_ffff {
        let Some(scalar) = char::from_u32(codepoint) else {
            continue;
        };
        let mut buffer = [0_u8; 4];
        let text = scalar.encode_utf8(&mut buffer);
        let width = if codepoint <= 0x7f {
            1
        } else if codepoint <= 0x7ff {
            2
        } else if codepoint <= 0xffff {
            3
        } else {
            4
        };
        assert_eq!(scalarLength(text.to_owned()), 1, "U+{codepoint:X}");
        assert_eq!(byteLength(text.to_owned()), width, "U+{codepoint:X}");
        checked += 1;
    }
    assert_eq!(checked, 1_112_064);
}

#[test]
fn mixed_strings_records_and_decoding_preserve_scalar_semantics() {
    for (text, scalars, bytes) in [
        ("", 0, 0),
        ("a", 1, 1),
        ("é", 1, 2),
        ("e\u{301}", 2, 3),
        ("🇺🇸", 2, 8),
        ("👩‍💻", 3, 11),
        ("水a", 2, 4),
        ("\r\n", 2, 2),
        ("\0", 1, 1),
        ("\u{feff}", 1, 3),
        ("\u{10ffff}a", 2, 5),
    ] {
        assert_eq!(scalarLength(text.to_owned()), scalars);
        assert_eq!(byteLength(text.to_owned()), bytes);
        assert_eq!(nestedLength(&Text { value: text.into() }), scalars);
        assert_eq!(
            entry(text.as_bytes().to_vec()),
            vec![u8::from(scalars == 2)]
        );
    }
    for invalid in [vec![0xff], vec![0xc0, 0xaf], vec![0xed, 0xa0, 0x80]] {
        assert_eq!(entry(invalid), vec![255]);
    }
}
