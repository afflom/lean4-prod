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

    quote! { #tokens }.into()
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
