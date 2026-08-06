//! wasm-bindgen shell for the portable Lean IR parser/code generator.

use prod_codegen::generate_module;
use prod_ir::parser::parse_module;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

#[derive(Debug, Clone, Deserialize, Serialize)]
struct Root {
    id: String,
    dependencies: Vec<String>,
    proof_term_size: u64,
    kernel_depth: u64,
}

#[derive(Debug, Deserialize)]
struct RootFile {
    roots: Vec<Root>,
}

#[derive(Debug, Serialize)]
struct ParetoFile {
    roots: Vec<Root>,
}

fn dominates(a: &Root, b: &Root) -> bool {
    a.proof_term_size <= b.proof_term_size
        && a.kernel_depth <= b.kernel_depth
        && (a.proof_term_size < b.proof_term_size || a.kernel_depth < b.kernel_depth)
}

/// Parse exported sexp IR and return generated Rust source.
#[wasm_bindgen]
pub fn generate(ir: &str) -> Result<String, JsValue> {
    let (_, module) = parse_module(ir)
        .map_err(|error| JsValue::from_str(&format!("IR parse error: {error:?}")))?;
    generate_module(&module)
        .map_err(|error| JsValue::from_str(&format!("code generation error: {error}")))
}

/// Return the proof roots on the (proof size, kernel depth) Pareto front.
#[wasm_bindgen]
pub fn roots_pareto(json: &str) -> Result<String, JsValue> {
    let file: RootFile = serde_json::from_str(json)
        .map_err(|error| JsValue::from_str(&format!("roots JSON error: {error}")))?;
    let roots = file
        .roots
        .iter()
        .enumerate()
        .filter(|(idx, candidate)| {
            !file
                .roots
                .iter()
                .enumerate()
                .any(|(other_idx, other)| other_idx != *idx && dominates(other, candidate))
        })
        .map(|(_, root)| root.clone())
        .collect();
    serde_json::to_string(&ParetoFile { roots })
        .map_err(|error| JsValue::from_str(&format!("roots JSON output error: {error}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generate_returns_rust() {
        let source = generate("(module M (def inc ((x Nat)) Nat (add x 1)))").unwrap();
        assert!(source.contains("pub fn inc"));
        assert!(source.contains("checked_add(1).expect(\"Lean Nat addition overflow\")"));
    }

    #[test]
    fn roots_pareto_returns_only_nondominated_roots() {
        let json = r#"{"roots":[
          {"id":"a","dependencies":[],"proof_term_size":2,"kernel_depth":2},
          {"id":"b","dependencies":[],"proof_term_size":3,"kernel_depth":3},
          {"id":"c","dependencies":[],"proof_term_size":1,"kernel_depth":4}
        ]}"#;
        let output: RootFile = serde_json::from_str(&roots_pareto(json).unwrap()).unwrap();
        assert_eq!(output.roots.iter().map(|root| root.id.as_str()).collect::<Vec<_>>(), ["a", "c"]);
    }
}
