//! Public, transport-only UTF-8 View contract; application semantics stay in IR.

use prod_codegen::{generate_text_view_v1, TextBrowserAdapterBinding, TextViewV1};

fn fixture() -> (TextViewV1, TextBrowserAdapterBinding) {
    (
        TextViewV1 {
            title: "Text <request>".into(),
            heading: "Request & response".into(),
            input_label: "Request".into(),
            submit_label: "Submit".into(),
            output_label: "Response".into(),
            input_error: "Invalid input".into(),
            response_error: "Invalid response".into(),
            max_input_bytes: 32,
            max_output_bytes: 64,
            model_id: "11".repeat(32),
            view_model_id: "22".repeat(32),
            generated_core_sha256: "33".repeat(32),
        },
        TextBrowserAdapterBinding {
            package_name: "text-view-adapter".into(),
            package_version: "0.1.0".into(),
            core_crate_name: "text-view-core".into(),
            core_crate_version: "0.1.0".into(),
            core_function: "invoke".into(),
        },
    )
}

#[test]
fn text_view_generates_both_closed_transports_deterministically() {
    let (view, binding) = fixture();
    let first = generate_text_view_v1(&view, &binding).unwrap();
    assert_eq!(first, generate_text_view_v1(&view, &binding).unwrap());
    assert_eq!(first.hologram_assets.len(), 3);
    assert_eq!(first.browser_assets.len(), 3);
    assert!(first.hologram_bundle.bytes.starts_with(b"HOLOVIEW\0\x01"));
    assert!(first.browser_assets.iter().any(|file| {
        file.path == "index.html"
            && String::from_utf8_lossy(&file.bytes).contains("Text &lt;request&gt;")
    }));
}

#[test]
fn text_view_rejects_zero_byte_caps_and_untrusted_adapter_identifiers() {
    let (view, binding) = fixture();
    let mut invalid = view.clone();
    invalid.max_input_bytes = 0;
    assert!(generate_text_view_v1(&invalid, &binding).is_err());
    invalid = view.clone();
    invalid.max_output_bytes = 0;
    assert!(generate_text_view_v1(&invalid, &binding).is_err());
    let mut invalid_binding = binding;
    invalid_binding.core_function = "invoke(); panic!()".into();
    assert!(generate_text_view_v1(&view, &invalid_binding).is_err());
}

#[test]
fn text_view_rejects_incomplete_metadata_and_noncanonical_bindings() {
    let (view, binding) = fixture();
    for index in 0..7 {
        let mut invalid = view.clone();
        [
            &mut invalid.title,
            &mut invalid.heading,
            &mut invalid.input_label,
            &mut invalid.submit_label,
            &mut invalid.output_label,
            &mut invalid.input_error,
            &mut invalid.response_error,
        ][index]
            .clear();
        assert!(generate_text_view_v1(&invalid, &binding).is_err());
    }
    for digest in [
        "",
        "ABCDEF",
        &"AA".repeat(32),
        &"00".repeat(31),
        &"00".repeat(33),
    ] {
        for index in 0..3 {
            let mut invalid = view.clone();
            *[
                &mut invalid.model_id,
                &mut invalid.view_model_id,
                &mut invalid.generated_core_sha256,
            ][index] = digest.into();
            assert!(generate_text_view_v1(&invalid, &binding).is_err());
        }
    }
    for function in [
        "_",
        "Self",
        "fn",
        "self",
        "crate",
        "1function",
        "invoke.value",
        "invoke\n",
    ] {
        let mut invalid = binding.clone();
        invalid.core_function = function.into();
        assert!(generate_text_view_v1(&view, &invalid).is_err());
    }
    for version in ["1", "1.0", "01.0.0", "1.0.0-beta", "1.0.0\"\n"] {
        let mut invalid = binding.clone();
        invalid.core_crate_version = version.into();
        assert!(generate_text_view_v1(&view, &invalid).is_err());
    }
    let mut invalid = binding.clone();
    invalid.package_name = binding.core_crate_name;
    assert!(generate_text_view_v1(&view, &invalid).is_err());
}

#[test]
fn text_metadata_cannot_introduce_markup_or_inline_code() {
    let (mut view, binding) = fixture();
    view.title = "</title><script>alert(1)</script>&\"'".into();
    view.input_error = "\";globalThis.compromised=true;//\n\0".into();
    let generated = generate_text_view_v1(&view, &binding).unwrap();
    let html = String::from_utf8(generated.browser_assets[2].bytes.clone()).unwrap();
    assert!(!html.contains("<script>alert"));
    assert!(html.contains("&lt;/title&gt;&lt;script&gt;alert(1)&lt;/script&gt;&amp;&quot;&#39;"));
    let script = String::from_utf8(generated.browser_assets[1].bytes.clone()).unwrap();
    assert!(script.contains("const INPUT_ERROR=\"\\\";globalThis.compromised=true;//\\n\\u0000\";"));
}
