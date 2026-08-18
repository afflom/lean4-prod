//! prod-macros: Procedural macros for generating Rust code from prod IR
//!
//! Thin wrapper only — all parsing lives in `prod-ir` and all codegen in
//! `prod-codegen`. Usage:
//! ```rust,ignore
//! prod_defs! { ir = "path/to/exported.ir" }
//! ```

use proc_macro::TokenStream;
use quote::quote;
use std::fs;
use std::path::PathBuf;

/// `prod_defs! { ir = "path/to/module.ir" }`
///
/// Reads a prod IR file at compile time and generates Rust functions.
/// The path is resolved relative to `CARGO_MANIFEST_DIR` of the invoking
/// crate, falling back to the process working directory (the workspace root
/// under cargo), like the legacy `uor_atlas_defs!` did.
#[proc_macro]
pub fn prod_defs(input: TokenStream) -> TokenStream {
    let input_str = input.to_string();

    // Parse `ir = "..."` from the token stream
    let path = input_str
        .split('=')
        .nth(1)
        .and_then(|s| s.trim().strip_prefix('"'))
        .and_then(|s| s.strip_suffix('"'))
        .expect(r#"Expected prod_defs! { ir = "path" }"#);

    let resolved = resolve_ir_path(path);
    let ir_content = fs::read_to_string(&resolved)
        .unwrap_or_else(|e| panic!("Failed to read IR file {}: {}", resolved.display(), e));

    let module = prod_ir::parser::parse_module(&ir_content)
        .map(|(_, m)| m)
        .unwrap_or_else(|e| panic!("Failed to parse IR: {:?}", e));

    let src = prod_codegen::generate_module(&module)
        .unwrap_or_else(|e| panic!("Failed to generate code: {}", e));

    let tokens = syn::parse_str::<proc_macro2::TokenStream>(&src)
        .unwrap_or_else(|e| panic!("Generated code did not parse as Rust: {}\n{}", e, src));

    // Make cargo rebuild the invoking crate when the IR file changes.
    //
    // Without this, cargo's only inputs are the invoking crate's own sources,
    // so `lake exe prod-export` rewriting a golden does NOT trigger
    // re-expansion: the crate keeps compiling against the IR text captured by
    // the last build. That silently voids the guarantee
    // `prod-codegen-compile-tests` exists to provide — "every future golden
    // bless is checked by rustc, not only by eye" — because a bless whose
    // consumer crate is otherwise unchanged is never recompiled at all. It is
    // the same failure shape as the shift defect: a green build reporting on
    // an input it did not read. Observed live — new conformance structures
    // appeared in `golden.ir` while the crate still compiled the previous
    // expansion, and `cargo test` passed until the crate was touched by hand.
    //
    // `include_str!` is the stable way to register a file dependency
    // (`proc_macro::tracked_path` is still unstable). It must be an ABSOLUTE
    // path: `include_str!` resolves relative to the source file holding the
    // invocation, whereas `ir = "..."` is relative to `CARGO_MANIFEST_DIR`,
    // and the two differ by however deep the invoking module sits. Emitted
    // only when the resolved path is absolute, which it is whenever cargo set
    // `CARGO_MANIFEST_DIR`; the bare-path fallback silently skips tracking
    // rather than emitting an `include_str!` that would resolve elsewhere.
    let tracking = if resolved.is_absolute() {
        let tracked: &str = &resolved.to_string_lossy();
        quote! { const _: &str = include_str!(#tracked); }
    } else {
        quote! {}
    };

    quote! { #tracking #tokens }.into()
}

fn resolve_ir_path(path: &str) -> PathBuf {
    if let Ok(dir) = std::env::var("CARGO_MANIFEST_DIR") {
        let candidate = PathBuf::from(dir).join(path);
        if candidate.exists() {
            return candidate;
        }
    }
    PathBuf::from(path)
}
