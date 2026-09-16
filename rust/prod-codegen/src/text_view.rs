//! Closed UTF-8 text transports. The generated core owns application semantics.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use crate::view::{
    file, html, json, sha256, valid_digest, valid_ident, valid_package, valid_version,
};
use crate::{generate_holoview_bundle, Error, GeneratedPackage, GeneratedViewV1, PackageFile};

/// Evaluated `prism.text-view/1` value. Strings are text, never markup or code.
///
/// Byte caps bound transport copies, not the application's own allocations.
/// The modeled core must independently bound its execution and allocations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextViewV1 {
    pub title: String,
    pub heading: String,
    pub input_label: String,
    pub submit_label: String,
    pub output_label: String,
    pub input_error: String,
    pub response_error: String,
    pub max_input_bytes: u32,
    pub max_output_bytes: u32,
    pub model_id: String,
    pub view_model_id: String,
    pub generated_core_sha256: String,
}

/// Exact registry dependency and exported `Vec<u8> -> Vec<u8>` core entrypoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextBrowserAdapterBinding {
    pub package_name: String,
    pub package_version: String,
    pub core_crate_name: String,
    pub core_crate_version: String,
    pub core_function: String,
}

fn validate(view: &TextViewV1, binding: &TextBrowserAdapterBinding) -> Result<(), Error> {
    if [
        &view.title,
        &view.heading,
        &view.input_label,
        &view.submit_label,
        &view.output_label,
        &view.input_error,
        &view.response_error,
    ]
    .iter()
    .any(|text| text.trim().is_empty())
        || view.max_input_bytes == 0
        || view.max_output_bytes == 0
        || !valid_digest(&view.model_id)
        || !valid_digest(&view.view_model_id)
        || !valid_digest(&view.generated_core_sha256)
    {
        return Err(Error::OpaqueType("invalid prism.text-view/1 value".into()));
    }
    if !valid_package(&binding.package_name)
        || !valid_package(&binding.core_crate_name)
        || !valid_version(&binding.package_version)
        || !valid_version(&binding.core_crate_version)
        || !valid_ident(&binding.core_function)
        || matches!(binding.core_function.as_str(), "_" | "Self")
        || binding.package_name == binding.core_crate_name
        || crate::RUST_KEYWORDS.contains(&binding.core_function.as_str())
        || crate::RUST_KEYWORDS.contains(&binding.core_crate_name.replace('-', "_").as_str())
    {
        return Err(Error::OpaqueType(
            "invalid text browser adapter binding".into(),
        ));
    }
    Ok(())
}

fn index_html(view: &TextViewV1) -> String {
    format!(
        "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><title>{}</title><link rel=\"stylesheet\" href=\"app.css\"></head><body><main><h1>{}</h1><form id=\"application-form\" novalidate><label for=\"request\">{}</label><textarea id=\"request\" name=\"request\" rows=\"8\" aria-describedby=\"result\"></textarea><button id=\"submit\" type=\"submit\">{}</button></form><label id=\"response-label\" for=\"result\">{}</label><output id=\"result\" for=\"request\" role=\"status\" aria-labelledby=\"response-label\" aria-live=\"polite\" aria-atomic=\"true\"></output></main><script type=\"module\" src=\"app.js\"></script></body></html>\n",
        html(&view.title), html(&view.heading), html(&view.input_label),
        html(&view.submit_label), html(&view.output_label),
    )
}

const CSS: &str = "*{box-sizing:border-box}body{margin:0;background:#f6f7fb;color:#172033;font-family:ui-sans-serif,system-ui,sans-serif}main{width:min(48rem,calc(100% - 2rem));margin:3rem auto;padding:2rem;border:1px solid #c9d1df;border-radius:.75rem;background:#fff}h1{margin-top:0}form{display:grid;gap:.75rem}label{font-weight:600}textarea,button{width:100%;min-height:2.75rem;border:1px solid #77839a;border-radius:.4rem;padding:.55rem;font:inherit}textarea{resize:vertical}button{background:#234fdb;color:#fff;font-weight:700;cursor:pointer}textarea:focus-visible,button:focus-visible{outline:3px solid #234fdb;outline-offset:3px}button:disabled{cursor:wait;opacity:.7}output{display:block;min-height:2rem;white-space:pre-wrap;overflow-wrap:anywhere;margin-top:.5rem}#response-label{display:block;margin-top:1.5rem}\n";

fn shared_javascript(view: &TextViewV1) -> String {
    format!(
        "const INPUT_LIMIT={};\nconst OUTPUT_LIMIT={};\nconst INPUT_ERROR={};\nconst RESPONSE_ERROR={};\n{}",
        view.max_input_bytes, view.max_output_bytes, json(&view.input_error),
        json(&view.response_error), include_str!("text_view_shared.js"),
    )
}

fn adapter(view: &TextViewV1, binding: &TextBrowserAdapterBinding) -> GeneratedPackage {
    let cargo = format!(
        "[package]\nname = \"{}\"\nversion = \"{}\"\nedition = \"2021\"\npublish = false\n\n[lib]\ncrate-type = [\"cdylib\"]\n\n[dependencies]\njs-sys = \"=0.3.99\"\nwasm-bindgen = \"=0.2.122\"\n{} = \"={}\"\n",
        binding.package_name, binding.package_version, binding.core_crate_name, binding.core_crate_version,
    );
    let source = format!(
        "use wasm_bindgen::prelude::*;\n\n// Transport copies allocate only after their byte limits are checked.\n// The core's own allocation bound remains an application-model obligation.\n#[wasm_bindgen]\npub fn invoke_bytes(input: JsValue) -> Result<js_sys::Uint8Array, JsValue> {{\n    let input = input.dyn_into::<js_sys::Uint8Array>().map_err(|_| JsValue::from_str(\"expected Uint8Array\"))?;\n    if input.length() > {} {{ return Err(JsValue::from_str(\"input byte limit\")); }}\n    let bytes = input.to_vec();\n    core::str::from_utf8(&bytes).map_err(|_| JsValue::from_str(\"invalid input UTF-8\"))?;\n    let output = {}::{}(bytes);\n    if output.len() > {} {{ return Err(JsValue::from_str(\"output byte limit\")); }}\n    core::str::from_utf8(&output).map_err(|_| JsValue::from_str(\"invalid output UTF-8\"))?;\n    Ok(js_sys::Uint8Array::from(output.as_slice()))\n}}\n",
        view.max_input_bytes, binding.core_crate_name.replace('-', "_"), binding.core_function, view.max_output_bytes,
    );
    let mut files = vec![file("Cargo.toml", cargo), file("src/lib.rs", source)];
    let records = records(&files);
    files.push(file("generation-manifest.json", format!(
        "{{\"core_crate\":{},\"core_function\":{},\"core_version\":{},\"files\":[{}],\"generated_core_sha256\":{},\"max_input_bytes\":{},\"max_output_bytes\":{},\"model_id\":{},\"profile\":\"prism.text-view/1\",\"schema\":\"lean4-prod/text-browser-adapter/1\",\"view_model_id\":{}}}\n",
        json(&binding.core_crate_name), json(&binding.core_function), json(&binding.core_crate_version), records,
        json(&view.generated_core_sha256), view.max_input_bytes, view.max_output_bytes, json(&view.model_id), json(&view.view_model_id),
    )));
    files.sort_by(|a, b| a.path.cmp(&b.path));
    GeneratedPackage { files }
}

fn records(files: &[PackageFile]) -> String {
    files
        .iter()
        .map(|item| {
            format!(
                "{{\"path\":{},\"sha256\":{}}}",
                json(&item.path),
                json(&sha256(&item.bytes))
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// Generate deterministic text assets, HOLOVIEW v1, and a wasm-bindgen adapter.
///
/// Allocates output files. Rejects empty labels, zero caps, malformed digests or
/// bindings, and assets beyond HOLOVIEW's existing packaging limits. This is a
/// transport projection, not validation of the caller's application semantics.
pub fn generate_text_view_v1(
    view: &TextViewV1,
    binding: &TextBrowserAdapterBinding,
) -> Result<GeneratedViewV1, Error> {
    validate(view, binding)?;
    let html = index_html(view);
    let shared = shared_javascript(view);
    let browser_js = format!(
        "import init,{{invoke_bytes}}from'./{}.js';\n{}\n{}",
        binding.core_crate_name.replace('-', "_"),
        shared,
        include_str!("text_view_browser.js")
    );
    let hologram_js = format!("{}\n{}", shared, include_str!("text_view_hologram.js"));
    let browser_assets = vec![
        file("app.css", CSS.to_string()),
        file("app.js", browser_js),
        file("index.html", html.clone()),
    ];
    let hologram_assets = vec![
        file("app.css", CSS.to_string()),
        file("app.js", hologram_js),
        file("index.html", html),
    ];
    let browser_adapter = adapter(view, binding);
    let hologram_bundle = generate_holoview_bundle(&hologram_assets)?;
    let view_manifest = file("view-manifest.json", format!(
        "{{\"browser_adapter\":[{}],\"generated_core_sha256\":{},\"hologram_bundle\":{{\"path\":{},\"sha256\":{}}},\"max_input_bytes\":{},\"max_output_bytes\":{},\"model_id\":{},\"profile\":\"prism.text-view/1\",\"projections\":[{{\"files\":[{}],\"target\":\"browser-wasm-bindgen\"}},{{\"files\":[{}],\"target\":\"hologram-intent-v1\"}}],\"schema\":\"lean4-prod/text-view-projection/1\",\"view_model_id\":{}}}\n",
        records(&browser_adapter.files), json(&view.generated_core_sha256), json(&hologram_bundle.path), json(&sha256(&hologram_bundle.bytes)),
        view.max_input_bytes, view.max_output_bytes, json(&view.model_id), records(&browser_assets), records(&hologram_assets), json(&view.view_model_id),
    ));
    Ok(GeneratedViewV1 {
        hologram_assets,
        hologram_bundle,
        browser_assets,
        browser_adapter,
        view_manifest,
    })
}
