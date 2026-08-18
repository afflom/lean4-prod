use super::*;
use alloc::string::ToString;
use prod_ir::parser::parse_module;

fn generate(ir: &str) -> String {
    let (_, module) = parse_module(ir).unwrap();
    generate_module(&module).unwrap()
}

fn generate_err(ir: &str) -> Error {
    let (_, module) = parse_module(ir).unwrap();
    generate_module(&module).unwrap_err()
}

#[test]
fn test_generate_class_index() {
    let ir = r#"
(module UorAtlas.Kernel
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))

  (def classIndex ((h2 Nat) (d Nat) (l Nat) (inst (named "UorAtlas.Instance"))) Nat
    (add Nat (mul Nat (call stride inst) h2)
         (add Nat (mul Nat (proj "UorAtlas.Instance" "O" inst) d) l)))

  (def belt ((inst (named "UorAtlas.Instance"))) Nat
    (mul Nat (call class_count inst)
         (shl Nat 1 (sub Nat (proj "UorAtlas.Instance" "O" inst) 1))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n\npub fn classIndex(h2: u64, d: u64, l: u64, inst: crate::Instance) -> Result<u64, crate::ComputeError> {\n    Ok(((((stride(inst)) as u64).checked_mul(h2).ok_or(crate::ComputeError::MulOverflow)?) as u64).checked_add((((((inst).O) as u64).checked_mul(d).ok_or(crate::ComputeError::MulOverflow)?) as u64).checked_add(l).ok_or(crate::ComputeError::AddOverflow)?).ok_or(crate::ComputeError::AddOverflow)?)\n}\n\npub fn belt(inst: crate::Instance) -> Result<u64, crate::ComputeError> {\n    Ok(((class_count(inst)) as u64).checked_mul(((1) as u64).checked_shl(u32::try_from((((inst).O) as u64).saturating_sub(1)).map_err(|_| crate::ComputeError::ShiftExponentTooLarge)?).ok_or(crate::ComputeError::ShiftOverflow)?).ok_or(crate::ComputeError::MulOverflow)?)\n}\n\n"
    );
}

#[test]
fn test_generate_match() {
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (cases x
      (alt "Some" (v) v)
      (default 0)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn f(x: u64) -> u64 {\n    match x {\n        Some(v) => {\n            return v;\n        }\n        _ => {\n            return 0;\n        }\n    }\n}\n\n"
    );
}

#[test]
fn test_generate_list_param_is_a_slice_and_return_is_a_buffer() {
    // Lean List: a parameter borrows as `&[T]` and matches with slice
    // patterns; a return builds into a caller-owned `&mut [T]`.
    let ir = r#"
(module M
  (def digitSum ((xs (List Nat))) Nat
    (cases xs
      (alt "List.nil" () 0)
      (alt "List.cons" (h t) (add Nat h (call digitSum t)))))
  (def digits ((n Nat)) (List Nat)
    (if (lt n 8)
        (ctor "List.cons" n (ctor "List.nil"))
        (ctor "List.cons" (mod Nat n 8) (call digits (div Nat n 8)))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn digitSum(xs: &[u64]) -> Result<u64, crate::ComputeError> {\n    match xs {\n        [] => {\n            return Ok(0);\n        }\n        [h, t @ ..] => {\n            let h = *h;\n            let t0 = digitSum(t)?;\n            let t1 = ((h) as u64).checked_add(t0).ok_or(crate::ComputeError::AddOverflow)?;\n            return Ok(t1);\n        }\n    }\n}\n\npub fn digits(n: u64, output: &mut [u64]) -> Result<usize, crate::ComputeError> {\n    let mut __len: usize = 0;\n    if (n < 8) {\n        if (__len < output.len()) {\n        } else {\n            return Err(crate::ComputeError::OutputTooSmall);\n        }\n        if let Some(__slot) = output.get_mut(__len) {\n            *__slot = n;\n            __len += 1;\n        }\n        return Ok(__len);\n    } else {\n        if (__len < output.len()) {\n        } else {\n            return Err(crate::ComputeError::OutputTooSmall);\n        }\n        if let Some(__slot) = output.get_mut(__len) {\n            *__slot = if (8) == 0 { n } else { (n) % (8) };\n            __len += 1;\n        }\n        let t0 = digits(if (8) == 0 { 0 } else { (n) / (8) }, output.get_mut(__len..).unwrap_or(&mut []))?;\n        __len += t0;\n        return Ok(__len);\n    }\n}\n\n"
    );
}

#[test]
fn test_generate_list_builder_resolves_anf_let_bindings() {
    // The exact shape prod-export emits for `digits`: LCNF is in A-normal
    // form, so every cons cell arrives as a `let`. Those bindings have no
    // runtime representation in buffer mode — they are resolved through the
    // builder environment, not materialized.
    let ir = r#"
(module UorAtlas.Kernel
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))

  (def digits ((fuel Nat) (n Nat) (i (named "UorAtlas.Instance"))) (List Nat)
    (cases fuel
      (alt "Nat.zero" () (let _x_46 (ctor "List.nil") _x_46))
      (alt "Nat.succ" (n_25)
        (let _x_47 (proj "UorAtlas.Instance" "O" i)
          (if (lt n _x_47)
            (let _x_55 (ctor "List.nil") (let _x_56 (ctor "List.cons" n _x_55) _x_56))
            (let _x_50 (mod Nat n _x_47)
              (let _x_51 (div Nat n _x_47)
                (let _x_52 (call digits n_25 _x_51 i)
                  (let _x_53 (ctor "List.cons" _x_50 _x_52) _x_53)))))))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n\npub fn digits(fuel: u64, n: u64, i: crate::Instance, output: &mut [u64]) -> Result<usize, crate::ComputeError> {\n    let mut __len: usize = 0;\n    match fuel {\n        0 => {\n            return Ok(__len);\n        }\n        _ => {\n            let n_25 = (fuel).saturating_sub(1);\n            let _x_47 = (i).O;\n            if (n < _x_47) {\n                if (__len < output.len()) {\n                } else {\n                    return Err(crate::ComputeError::OutputTooSmall);\n                }\n                if let Some(__slot) = output.get_mut(__len) {\n                    *__slot = n;\n                    __len += 1;\n                }\n                return Ok(__len);\n            } else {\n                let _x_50 = if (_x_47) == 0 { n } else { (n) % (_x_47) };\n                let _x_51 = if (_x_47) == 0 { 0 } else { (n) / (_x_47) };\n                if (__len < output.len()) {\n                } else {\n                    return Err(crate::ComputeError::OutputTooSmall);\n                }\n                if let Some(__slot) = output.get_mut(__len) {\n                    *__slot = _x_50;\n                    __len += 1;\n                }\n                let t0 = digits(n_25, _x_51, i, output.get_mut(__len..).unwrap_or(&mut []))?;\n                __len += t0;\n                return Ok(__len);\n            }\n        }\n    }\n}\n\n"
    );
}

#[test]
fn test_generate_zero_arg_list_golden_is_a_promoted_static_slice() {
    let ir = r#"
(module UorAtlas.Goldens
  (def golden_digits_43_canonical () (List Nat)
    (ctor "List.cons" 3 (ctor "List.cons" 5 (ctor "List.nil"))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn golden_digits_43_canonical() -> &'static [u64] {\n    &[3, 5]\n}\n\n"
    );
}

#[test]
fn test_fallibility_is_precise_not_uniform() {
    // Only definitions that can actually fail carry `Result`, and that
    // property propagates through the call graph — including recursion.
    let ir = r#"
(module M
  (def pure ((x Nat) (y Nat)) Nat (sub Nat x y))
  (def viaDiv ((x Nat)) Nat (call pure (div Nat x 2) 1))
  (def risky ((x Nat)) Nat (add Nat x 1))
  (def caller ((x Nat)) Nat (call risky x))
  (def loops ((fuel Nat) (x Nat)) Nat
    (cases fuel
      (alt "Nat.zero" () x)
      (alt "Nat.succ" (k) (call loops k (add Nat x 1)))))
)
"#;
    let out = generate(ir);
    assert!(out.contains("pub fn pure(x: u64, y: u64) -> u64 {"));
    assert!(out.contains("pub fn viaDiv(x: u64) -> u64 {"));
    assert!(out.contains("pub fn risky(x: u64) -> Result<u64, crate::ComputeError> {"));
    assert!(out.contains("pub fn caller(x: u64) -> Result<u64, crate::ComputeError> {"));
    assert!(out.contains("Ok(risky(x)?)"));
    // A recursive definition reaches its own fixpoint.
    assert!(out.contains("pub fn loops(fuel: u64, x: u64) -> Result<u64, crate::ComputeError> {"));
    // The argument is computed into a branch-local temporary and passed by
    // name: a `TryLet` inside a match arm is never folded into its use, so
    // the checked add cannot be evaluated on the arm that does not run.
    assert!(out.contains("checked_add(1).ok_or(crate::ComputeError::AddOverflow)?;"));
    assert!(out.contains("loops(k, "));
}

#[test]
fn test_intermediate_list_value_is_a_codegen_error() {
    // A list that flows anywhere other than the output buffer would need an
    // owned representation; fail honestly instead of allocating one.
    let ir = r#"
(module M
  (def digitSum ((xs (List Nat))) Nat
    (cases xs
      (alt "List.nil" () 0)
      (alt "List.cons" (h t) h)))
  (def digits ((n Nat)) (List Nat) (ctor "List.nil"))
  (def total ((n Nat)) Nat (call digitSum (call digits n)))
)
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnsupportedList(
            "`digits` returns a list; its result cannot be used as an intermediate value"
                .to_string()
        )
    );
}

#[test]
fn test_nested_list_type_is_a_codegen_error() {
    let ir = r#"
(module M
  (def f ((x Nat)) (Option (List Nat)) (ctor "Option.none"))
)
"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedList(_)));
}

#[test]
fn test_vec_type_is_rejected_as_heap_allocating() {
    let ir = r#"
(module M
  (def f ((xs (Vec Nat))) Nat 0)
)
"#;
    // The payload names the offending type in the IR's own spelling: the
    // rejection is made in `prod-lower`, which has no business knowing Rust's
    // type names.
    assert_eq!(generate_err(ir), Error::HeapType("(Vec Nat)".to_string()));
}

#[test]
fn test_computed_zero_arg_list_is_a_codegen_error() {
    // A golden whose elements are computed cannot be a promoted static slice.
    let ir = r#"
(module M
  (def g () (List Nat) (ctor "List.cons" (add Nat 1 2) (ctor "List.nil")))
)
"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedList(_)));
}

#[test]
fn test_generate_option_and_bool() {
    // Option/Bool ctors and match arms map to Rust's native types.
    let ir = r#"
(module M
  (def tryDecode ((idx Nat)) (Option Nat)
    (if (le idx 96) (ctor "Option.some" idx) (ctor "Option.none")))
  (def fromOpt ((x (Option Nat))) Bool
    (cases x
      (alt "Option.some" (v) (ctor "Bool.true"))
      (alt "Option.none" () (ctor "Bool.false"))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn tryDecode(idx: u64) -> Option<u64> {\n    if (idx <= 96) {\n        return Some(idx);\n    } else {\n        return None;\n    }\n}\n\npub fn fromOpt(x: Option<u64>) -> bool {\n    match x {\n        Some(v) => {\n            return true;\n        }\n        None => {\n            return false;\n        }\n    }\n}\n\n"
    );
}

#[test]
fn test_generate_nat_cases_recursion() {
    // LCNF structural recursion on Nat: `Nat.zero` → literal `0` pattern,
    // `Nat.succ k` → `_` arm with the predecessor bound via saturating_sub.
    let ir = r#"
(module M
  (def digitCount ((fuel Nat) (n Nat)) Nat
    (cases fuel
      (alt "Nat.zero" () 0)
      (alt "Nat.succ" (k) (if (lt n 8) 1 (add Nat 1 (call digitCount k (div Nat n 8)))))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn digitCount(fuel: u64, n: u64) -> Result<u64, crate::ComputeError> {\n    match fuel {\n        0 => {\n            return Ok(0);\n        }\n        _ => {\n            let k = (fuel).saturating_sub(1);\n            if (n < 8) {\n                return Ok(1);\n            } else {\n                let t0 = digitCount(k, if (8) == 0 { 0 } else { (n) / (8) })?;\n                let t1 = ((1) as u64).checked_add(t0).ok_or(crate::ComputeError::AddOverflow)?;\n                return Ok(t1);\n            }\n        }\n    }\n}\n\n"
    );
}

#[test]
fn test_generate_ctor_proj() {
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (proj "Pair" "fst" (ctor "Pair" x 2)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn f(x: u64) -> u64 {\n    (Pair(x, 2)).fst\n}\n\n"
    );
}

#[test]
fn test_generate_projection_uses_field_names() {
    let ir = r#"
(module UorAtlas.Kernel
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
  (def decode ((i (named "UorAtlas.Instance"))) (Tuple Nat (Tuple Nat Nat))
    (ctor "Prod.mk" (proj "UorAtlas.Instance" "q" i)
      (ctor "Prod.mk" (proj "UorAtlas.Instance" "O" i) 1)))
)
"#;
    let out = generate(ir);
    assert!(out.contains("((i).q, ((i).O, 1))"));
}

#[test]
fn test_projection_of_keyword_field_is_raw_escaped() {
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (type Nat)))
  (def get ((r (named "M.Rec"))) Nat (proj "M.Rec" "type" r)))
"#;
    let out = generate(ir);
    assert!(out.contains("(r).r#type"));
}

#[test]
fn test_generate_kernel_ir_shapes() {
    // The exact def shapes prod-export emits for stride and classDecode
    // (see rust/prod-core/kernel.ir).
    let ir = r#"
(module UorAtlas.Kernel
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))

  (def stride ((i (named "UorAtlas.Instance"))) Nat
    (let _x_4 (proj "UorAtlas.Instance" "T" i) (let _x_5 (proj "UorAtlas.Instance" "O" i) (let _x_13 (mul Nat _x_4 _x_5) _x_13))))

  (def classDecode ((idx Nat) (i (named "UorAtlas.Instance"))) (Tuple Nat (Tuple Nat Nat))
    (let _x_4 (call stride i) (let h2 (div Nat idx _x_4) (let rem (mod Nat idx _x_4) (let _x_10 (proj "UorAtlas.Instance" "O" i) (let d (div Nat rem _x_10) (let l (mod Nat rem _x_10) (let _x_13 (ctor "Prod.mk" d l) (let _x_14 (ctor "Prod.mk" h2 _x_13) _x_14)))))))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n\npub fn stride(i: crate::Instance) -> Result<u64, crate::ComputeError> {\n    let _x_4 = (i).T;\n    let _x_5 = (i).O;\n    let _x_13 = ((_x_4) as u64).checked_mul(_x_5).ok_or(crate::ComputeError::MulOverflow)?;\n    Ok(_x_13)\n}\n\npub fn classDecode(idx: u64, i: crate::Instance) -> Result<(u64, (u64, u64)), crate::ComputeError> {\n    let _x_4 = stride(i)?;\n    let h2 = if (_x_4) == 0 { 0 } else { (idx) / (_x_4) };\n    let rem = if (_x_4) == 0 { idx } else { (idx) % (_x_4) };\n    let _x_10 = (i).O;\n    let d = if (_x_10) == 0 { 0 } else { (rem) / (_x_10) };\n    let l = if (_x_10) == 0 { rem } else { (rem) % (_x_10) };\n    let _x_13 = (d, l);\n    let _x_14 = (h2, _x_13);\n    Ok(_x_14)\n}\n\n"
    );
}

#[test]
fn test_undeclared_dotted_ctor_is_rejected_not_rendered_as_a_path() {
    // This used to render `(Unknown.Struct(x)).count` and exit 0. A dotted
    // Lean name is not a Rust path in expression position — `A.B(x)` parses
    // as a field access on a value named `A` followed by a call, so even
    // `syn::parse_str` accepts it and the breakage lands in rustc, far from
    // the IR that caused it. It is now an `UnresolvedCall` naming the ctor.
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (proj "Unknown.Struct" "count" (ctor "Unknown.Struct" x)))
)
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnresolvedCall("Unknown.Struct".to_string())
    );
}

#[test]
fn test_undeclared_dot_free_ctor_still_renders_as_a_bare_path() {
    // The complement of the test above: a dot-free constructor name is at
    // least a syntactically valid Rust path, so the bare-name fallthrough is
    // left intact for hosts that supply the type by hand.
    let ir = r#"
(module M
  (def f ((x Nat)) Nat (ctor "Pair" x 2))
)
"#;
    assert!(generate(ir).contains("Pair(x, 2)"));
}

#[test]
fn test_ctor_in_a_definition_body_only_is_rejected_when_undeclared() {
    // The end-to-end shape of the bug: a definition whose body constructs and
    // projects a type that is not declared in the module. `Lower.lean` now
    // declares body-reachable types (`declTypeNames`), so this IR is what
    // reaches codegen only when the declaration really is missing — and then
    // it must fail, not emit `Conformance.NoProp.mk(n, n)`.
    let ir = r#"
(module Conformance
  (def c_ctor_body_only ((n Nat)) Nat
    (let _x_1 (ctor "Conformance.NoProp.mk" n n)
      (let _x_2 (proj "Conformance.NoProp" "alpha" _x_1) _x_2)))
)
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnresolvedCall("Conformance.NoProp.mk".to_string())
    );
}

#[test]
fn test_ctor_in_a_definition_body_only_renders_when_declared() {
    // The same IR with the declaration `Lower.lean` now emits for it.
    let ir = r#"
(module Conformance
  (type "Conformance.NoProp"
    (ctor "Conformance.NoProp.mk" (alpha Nat) (beta Nat)))
  (def c_ctor_body_only ((n Nat)) Nat
    (let _x_1 (ctor "Conformance.NoProp.mk" n n)
      (let _x_2 (proj "Conformance.NoProp" "alpha" _x_1) _x_2)))
)
"#;
    let out = generate(ir);
    assert!(out.contains("pub struct NoProp {"));
    assert!(out.contains("crate::NoProp { alpha: n, beta: n }"));
    assert!(out.contains("(_x_1).alpha"));
}

/// Every `Error` variant must appear in the published rejection table
/// (`REJECTIONS`, rendered into `specs/lean-for-production.md`). The two are
/// separate lists that have to agree, and nothing but this test makes them:
/// a new variant would otherwise vanish from the contract while
/// `just subset-check` still passed.
///
/// The match below is exhaustive on purpose — no wildcard arm — so adding an
/// `Error` variant is a *compile* error here, not a silently-passing test.
#[test]
fn test_every_error_variant_is_published_in_rejections() {
    let s = || String::from("x");
    let all = [
        Error::OpaqueExpr(s()),
        Error::ParamOutOfBounds(0),
        Error::UnsupportedList(s()),
        Error::HeapType(s()),
        Error::RecursiveType(s()),
        Error::PolymorphicType(s()),
        Error::UnsupportedFieldType(s()),
        Error::DuplicateTypeName(s()),
        Error::OpaqueType(s()),
        Error::UnresolvedCall(s()),
        Error::UnknownField(s(), s()),
        Error::UnsupportedJoinPoint(s()),
        Error::UnsupportedKind(s()),
        Error::ReservedFieldName(s(), s()),
    ];

    for error in &all {
        let name = match error {
            Error::OpaqueExpr(_) => "OpaqueExpr",
            Error::ParamOutOfBounds(_) => "ParamOutOfBounds",
            Error::UnsupportedList(_) => "UnsupportedList",
            Error::HeapType(_) => "HeapType",
            Error::RecursiveType(_) => "RecursiveType",
            Error::PolymorphicType(_) => "PolymorphicType",
            Error::UnsupportedFieldType(_) => "UnsupportedFieldType",
            Error::DuplicateTypeName(_) => "DuplicateTypeName",
            Error::OpaqueType(_) => "OpaqueType",
            Error::UnresolvedCall(_) => "UnresolvedCall",
            Error::UnknownField(..) => "UnknownField",
            Error::UnsupportedJoinPoint(_) => "UnsupportedJoinPoint",
            Error::UnsupportedKind(_) => "UnsupportedKind",
            Error::ReservedFieldName(..) => "ReservedFieldName",
        };
        assert!(
            REJECTIONS.iter().any(|(variant, _)| *variant == name),
            "`Error::{}` is not in REJECTIONS, so the published subset contract does not disclose it",
            name
        );
    }

    // ...and no entry in REJECTIONS without a matching variant.
    assert_eq!(
        REJECTIONS.len(),
        all.len(),
        "REJECTIONS lists {} rejections for {} Error variants",
        REJECTIONS.len(),
        all.len()
    );
}

#[test]
fn test_unsupported_field_type_names_the_type_and_the_field() {
    // The milestone's promise is that a rejection names the Lean constant
    // responsible; "a list field would need owned storage" alone did not.
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (xs (List Nat)))))
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnsupportedFieldType(
            "`M.Rec.xs`: a list field would need owned storage".to_string()
        )
    );

    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (xs (Vec Nat)))))
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnsupportedFieldType(
            "`M.Rec.xs`: a vector field would need heap storage".to_string()
        )
    );
}

#[test]
fn test_generate_zero_param_golden_def() {
    // The shape prod-export uses for goldens.ir entries.
    let ir = r#"
(module UorAtlas.Goldens
  (def golden_stride_canonical () Nat 24)

  (def golden_classDecode_43_canonical () (Tuple Nat (Tuple Nat Nat))
    (ctor "Prod.mk" 1 (ctor "Prod.mk" 2 3)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn golden_stride_canonical() -> u64 {\n    24\n}\n\npub fn golden_classDecode_43_canonical() -> (u64, (u64, u64)) {\n    (1, (2, 3))\n}\n\n"
    );
}

#[test]
fn test_generate_jp_jmp_inlined() {
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (let g (jp g (a) (add Nat a 1)) (jmp g x)))
)
"#;
    let out = generate(ir);
    // The `let` LCNF wraps the declaration in disappears entirely rather than
    // binding a unit nobody reads: the join point has one jump site, and its
    // body belongs there.
    assert_eq!(
        out,
        "pub fn f(x: u64) -> Result<u64, crate::ComputeError> {\n    let a = x;\n    Ok(((a) as u64).checked_add(1).ok_or(crate::ComputeError::AddOverflow)?)\n}\n\n"
    );
}

#[test]
fn test_cyclic_join_point_is_rejected() {
    // This used to emit a `loop { /* manual port required */ }` skeleton at
    // exit 0. That skeleton never bound the join point's parameter and left
    // `()` where the arm needed a value, so it was Rust that did not compile —
    // the same silently-broken output this crate rejects everywhere else.
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (jp loop (i) (if (lt i 10) (jmp loop (add Nat i 1)) i)))
)
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnsupportedJoinPoint("loop".to_string())
    );
}

#[test]
fn test_multi_caller_join_point_is_rejected() {
    // Two `jmp` sites for one `jp`. LCNF produces this from something as
    // ordinary as a `match` whose arms both feed a shared continuation, so it
    // is not an exotic corner — see `Conformance.c_ctor_body_only`.
    let ir = r#"
(module M
  (def f ((c Nat) (x Nat)) Nat
    (let g (jp g (a) (add Nat a 1))
      (if (lt c 1) (jmp g x) (jmp g c))))
)
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnsupportedJoinPoint("g".to_string())
    );
}

#[test]
fn test_join_point_with_no_callers_still_renders() {
    // The two supported forms are unaffected: no callers renders the body in
    // place, and exactly one caller inlines (covered above).
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (jp g (a) x))
)
"#;
    // Nothing jumps to `g`, so its body IS the definition's body and renders
    // in place -- no binding, no placeholder.
    assert_eq!(generate(ir), "pub fn f(x: u64) -> u64 {\n    x\n}\n\n");
}

#[test]
fn test_generate_pow() {
    let ir = r#"
(module M
  (def belt ((i Nat)) Nat
    (pow Nat 2 (sub Nat i 1)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn belt(i: u64) -> Result<u64, crate::ComputeError> {\n    Ok(((2) as u64).checked_pow(u32::try_from(((i) as u64).saturating_sub(1)).map_err(|_| crate::ComputeError::PowExponentTooLarge)?).ok_or(crate::ComputeError::PowOverflow)?)\n}\n\n"
    );
}

#[test]
fn test_generate_shr() {
    // `Nat.shiftRight` is total and infallible (Lean's `Nat` is unbounded, so
    // `a >>> b = 0` once `b >= 64` and `a` fits `u64`): no `ComputeError`
    // variant, no `?`, just `checked_shr(..).unwrap_or(0)`.
    let ir = r#"
(module M
  (def half ((n Nat) (k Nat)) Nat
    (shr Nat n k))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn half(n: u64, k: u64) -> u64 {\n    ((n) as u64).checked_shr(u32::try_from(k).unwrap_or(u32::MAX)).unwrap_or(0)\n}\n\n"
    );
}

#[test]
fn test_generate_decide_unwrapped_comparison_is_a_plain_bool() {
    // Mirrors the IR shape `lean/Prod/Lower.lean`'s `decideOf?` produces for
    // `Conformance.c_bool` (`a < b : Bool`, not consumed by an `if`): a
    // decidable comparison bound directly to a `Bool`-typed `let` renders as
    // a plain Rust comparison, never round-tripping through `Decidable`.
    let ir = r#"
(module M
  (def c_bool ((a Nat) (b Nat)) Bool
    (let x (lt a b) x))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn c_bool(a: u64, b: u64) -> bool {\n    let x = (a < b);\n    x\n}\n\n"
    );
}

#[test]
fn test_generate_nat_arithmetic_policy_never_panics() {
    let ir = r#"
(module M
  (def add ((x Nat) (y Nat)) Nat (add Nat x y))
  (def sub ((x Nat) (y Nat)) Nat (sub Nat x y))
  (def div ((x Nat) (y Nat)) Nat (div Nat x y))
  (def modu ((x Nat) (y Nat)) Nat (mod Nat x y))
  (def shl ((x Nat) (y Nat)) Nat (shl Nat x y))
  (def pow ((x Nat) (y Nat)) Nat (pow Nat x y))
)
"#;
    let out = generate(ir);
    assert!(out.contains("checked_add(y).ok_or(crate::ComputeError::AddOverflow)?"));
    assert!(out.contains("saturating_sub(y)"));
    assert!(out.contains("if (y) == 0 { 0 } else { (x) / (y) }"));
    assert!(out.contains("if (y) == 0 { x } else { (x) % (y) }"));
    assert!(out.contains("checked_shl(u32::try_from(y).map_err(|_| crate::ComputeError::ShiftExponentTooLarge)?).ok_or(crate::ComputeError::ShiftOverflow)?"));
    assert!(out.contains("checked_pow(u32::try_from(y).map_err(|_| crate::ComputeError::PowExponentTooLarge)?).ok_or(crate::ComputeError::PowOverflow)?"));
    // The whole point: no panicking exit remains in the arithmetic lowering.
    assert!(!out.contains(".expect("));
    assert!(!out.contains(".unwrap("));
    assert!(!out.contains("panic!"));
}

#[test]
fn test_generate_unreachable() {
    let ir = "(module M (def f ((x Nat)) Nat (unreachable)))";
    let out = generate(ir);
    // A `Fail` is a terminator, so it prints as one.
    assert_eq!(out, "pub fn f(x: u64) -> u64 {\n    unreachable!();\n}\n\n");
}

#[test]
fn test_param_out_of_bounds_is_an_error() {
    let ir = "(module M (def f ((x Nat)) Nat (param 5)))";
    let (_, module) = parse_module(ir).unwrap();
    assert_eq!(generate_module(&module), Err(Error::ParamOutOfBounds(5)));
}

#[test]
fn test_extern_call_is_rejected_not_emitted() {
    // Before this, an untagged callee still rendered as a plain Rust call to a
    // function nobody defined, and the failure surfaced far away in rustc.
    let ir = r#"(module M (def f ((x Nat)) Nat (extern "Foo.helper" x)))"#;
    assert_eq!(
        generate_err(ir),
        Error::UnresolvedCall("Foo.helper".to_string())
    );
}

#[test]
fn test_generate_struct_from_single_ctor_type() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
  (def stride ((i (named "UorAtlas.Instance"))) Nat 0)
)
"#;
    let out = generate(ir);
    assert!(out.contains(
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n"
    ));
    assert!(out.contains("pub fn stride(i: crate::Instance) -> u64 {"));
}

#[test]
fn test_generate_enum_from_multi_ctor_type() {
    let ir = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat)))
)
"#;
    let out = generate(ir);
    assert!(out.contains(
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub enum Shape {\n    circle { radius: u64 },\n    rect { w: u64, h: u64 },\n}\n"
    ));
}

#[test]
fn test_generate_fieldless_ctor_renders_unit_variant() {
    let ir = r#"
(module M
  (type "M.Flag" (ctor "M.Flag.off") (ctor "M.Flag.on")))
"#;
    let out = generate(ir);
    assert!(out.contains("pub enum Flag {\n    off,\n    on,\n}\n"));
}

#[test]
fn test_rust_keyword_field_names_are_raw_escaped() {
    // A Lean field named `type` or `fn` is legal Lean and illegal Rust.
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (type Nat) (fn Nat))))
"#;
    let out = generate(ir);
    assert!(out.contains("pub r#type: u64"));
    assert!(out.contains("pub r#fn: u64"));
}

#[test]
fn test_recursive_type_is_rejected() {
    let ir = r#"
(module M
  (type "M.Tree"
    (ctor "M.Tree.leaf")
    (ctor "M.Tree.node" (left (named "M.Tree")) (right (named "M.Tree")))))
"#;
    assert_eq!(generate_err(ir), Error::RecursiveType("M.Tree".to_string()));
}

#[test]
fn test_duplicate_last_component_is_rejected() {
    let ir = r#"
(module M
  (type "A.Thing" (ctor "A.Thing.mk" (x Nat)))
  (type "B.Thing" (ctor "B.Thing.mk" (y Nat))))
"#;
    assert_eq!(
        generate_err(ir),
        Error::DuplicateTypeName("Thing".to_string())
    );
}

#[test]
fn test_polymorphic_type_is_rejected_with_its_reason() {
    // The exporter cannot describe a parameterised inductive, so it declares
    // the type as unsupported rather than omitting it — that turns a generic
    // "unknown type" into a rejection that names monomorphization.
    let ir = r#"(module M (type "M.Box" (unsupported "type parameters")))"#;
    assert_eq!(
        generate_err(ir),
        Error::PolymorphicType("M.Box".to_string())
    );
}

#[test]
fn test_undeclared_named_type_in_a_signature_is_rejected() {
    let ir = r#"(module M (def f ((x (named "M.Nope"))) Nat 0))"#;
    assert!(matches!(generate_err(ir), Error::OpaqueType(_)));
}

#[test]
fn test_undeclared_named_type_in_a_return_position_is_rejected() {
    let ir = r#"(module M (def f ((x Nat)) (named "M.Nope") x))"#;
    assert!(matches!(generate_err(ir), Error::OpaqueType(_)));
}

#[test]
fn test_generate_named_struct_construction() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
  (def mk ((a Nat) (b Nat) (c Nat)) (named "UorAtlas.Instance")
    (ctor "UorAtlas.Instance.mk" a b c)))
"#;
    let out = generate(ir);
    assert!(out.contains("crate::Instance { q: a, T: b, O: c }"));
}

#[test]
fn test_generate_enum_construction_and_patterns() {
    let ir = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat)))
  (def area ((s (named "M.Shape"))) Nat
    (cases s
      (alt "M.Shape.circle" (r) r)
      (alt "M.Shape.rect" (w h) (mul Nat w h))))
  (def unit ((r Nat)) (named "M.Shape") (ctor "M.Shape.circle" r)))
"#;
    let out = generate(ir);
    assert!(out.contains("crate::Shape::circle { radius: r } => {"));
    assert!(out.contains("crate::Shape::rect { w: w, h: h } =>"));
    assert!(out.contains("crate::Shape::circle { radius: r }"));
}

#[test]
fn test_ctor_arity_mismatch_is_an_error() {
    let ir = r#"
(module M
  (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat)))
  (def f ((x Nat)) (named "M.Pair") (ctor "M.Pair.mk" x)))
"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedFieldType(_)));
}

#[test]
fn test_cases_alt_arity_mismatch_on_a_declared_ctor_is_an_error() {
    // The alt names a declared two-field constructor but binds only one
    // binder. Falling through to the positional fallback would render
    // `M.Pair.mk(x) => ...` — a dotted name as a Rust path with a
    // positional pattern, which does not compile. This must be rejected,
    // symmetric with the construction-side arity check.
    let ir = r#"
(module M
  (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat)))
  (def f ((p (named "M.Pair"))) Nat
    (cases p
      (alt "M.Pair.mk" (x) x))))
"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedFieldType(_)));
}

#[test]
fn test_cases_alt_on_an_undeclared_ctor_still_falls_through() {
    // Regression guard: an alt naming a constructor that is NOT in this
    // module's type table (not even the same arity check applies) must keep
    // the existing positional-fallback rendering untouched.
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (cases x
      (alt "Foo.Bar" (a b) (add Nat a b))
      (default 0))))
"#;
    let out = generate(ir);
    assert!(out.contains("Foo.Bar(a, b) => "));
}

#[test]
fn test_opaque_type_is_rejected_not_injected() {
    // Previously rendered the raw Lean name as a Rust type, which exploded
    // inside syn::parse_str with an error pointing nowhere near the cause.
    let ir = r#"(module M (def f ((x (opaque "Foo.Bar"))) Nat 0))"#;
    assert_eq!(generate_err(ir), Error::OpaqueType("Foo.Bar".to_string()));
}

#[test]
fn test_projection_of_an_undeclared_field_is_rejected() {
    // A projection must name a field its type actually declares. Without this,
    // a declaration and a projection can disagree inside one IR file and still
    // compile, as long as something else supplies a type with the other
    // spelling.
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (alpha Nat)))
  (def f ((r (named "M.Rec"))) Nat (proj "M.Rec" "beta" r)))
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnknownField("M.Rec".to_string(), "beta".to_string())
    );
}

#[test]
fn test_projection_of_a_declared_field_still_renders() {
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (alpha Nat)))
  (def f ((r (named "M.Rec"))) Nat (proj "M.Rec" "alpha" r)))
"#;
    assert!(generate(ir).contains("(r).alpha"));
}

#[test]
fn test_int_division_is_euclidean_not_truncating() {
    // Lean's Div Int / Mod Int instances use Int.ediv / Int.emod — its own
    // docs say so, "for compatibility with SMT-LIB". Rust's / and % truncate.
    // They differ for every negative operand: Lean gives (-12) % 7 = 2, Rust
    // gives -5. Rendering / and % here would be silently wrong, and every test
    // with non-negative inputs would still pass.
    let ir = r#"(module M (def f ((a Int) (b Int)) Int (div Int a b)))"#;
    let out = generate(ir);
    assert!(out.contains("checked_div_euclid"), "got: {}", out);
    assert!(
        !out.contains("(a) / (b)"),
        "must not render truncating division"
    );
    // Int.ediv is total on a zero divisor (Init/Data/Int/DivMod/Basic.lean:76
    // is explicit: `| -[_+1], 0 => 0`), so the zero-guard stays.
    assert!(out.contains("if (b) == 0 { 0 }"), "got: {}", out);
}

#[test]
fn test_int_modulo_is_euclidean() {
    let ir = r#"(module M (def f ((a Int) (b Int)) Int (mod Int a b)))"#;
    assert!(generate(ir).contains("checked_rem_euclid"));
}

#[test]
fn test_modulo_by_zero_is_the_dividend_not_zero() {
    // Lean `Nat.mod`'s own doc comment: "When the divisor is `0`, the result
    // is the dividend rather than an error" (doctest `5 % 0 = 5`); `Int`'s
    // `emod_zero : a % 0 = a` (doctest `(7 : Int) % (0 : Int) = 7`). Division
    // by zero really is `0` for both kinds — only modulo's zero branch must
    // be the dividend, not a copy-pasted `0`.
    let nat = generate(r#"(module M (def f ((a Nat) (b Nat)) Nat (mod Nat a b)))"#);
    assert!(
        nat.contains("if (b) == 0 { a } else"),
        "Nat mod-by-zero must be the dividend: got {}",
        nat
    );

    let int = generate(r#"(module M (def f ((a Int) (b Int)) Int (mod Int a b)))"#);
    assert!(
        int.contains("if (b) == 0 { a } else"),
        "Int mod-by-zero must be the dividend: got {}",
        int
    );

    // Division by zero is unaffected: still `0` for both kinds.
    let nat_div = generate(r#"(module M (def f ((a Nat) (b Nat)) Nat (div Nat a b)))"#);
    assert!(nat_div.contains("if (b) == 0 { 0 } else"));
    let int_div = generate(r#"(module M (def f ((a Int) (b Int)) Int (div Int a b)))"#);
    assert!(int_div.contains("if (b) == 0 { 0 } else"));
}

#[test]
fn test_int_sub_is_checked_unlike_nat() {
    // Nat subtraction truncates at zero and cannot fail; Int subtraction can
    // overflow i64, because Lean's Int is unbounded and i64 is not.
    let nat = generate(r#"(module M (def f ((a Nat) (b Nat)) Nat (sub Nat a b)))"#);
    assert!(nat.contains("saturating_sub"));
    assert!(nat.contains("-> u64 {"), "Nat sub is infallible");

    let int = generate(r#"(module M (def f ((a Int) (b Int)) Int (sub Int a b)))"#);
    assert!(int.contains("checked_sub(b).ok_or(crate::ComputeError::SubOverflow)?"));
    assert!(int.contains("-> Result<i64, crate::ComputeError>"));
}

#[test]
fn test_int_neg_is_checked() {
    let ir = r#"(module M (def f ((a Int)) Int (neg Int a)))"#;
    let out = generate(ir);
    assert!(out.contains("checked_neg().ok_or(crate::ComputeError::NegOverflow)?"));
}

#[test]
fn test_neg_on_a_non_int_kind_is_rejected() {
    let ir = r#"(module M (def f ((a Nat)) Nat (neg Nat a)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}

#[test]
fn test_int_shifts_are_rejected() {
    // Deliberate non-goal; rejected precisely rather than rendered.
    let ir = r#"(module M (def f ((a Int) (b Int)) Int (shl Int a b)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}

#[test]
fn test_int_literal_ctors_render_not_unresolved() {
    // `(1 : Int)`/`(0 : Int)` elaborate through Int's own constructors
    // (`Int.ofNat`/`Int.negSucc`), not a bare numeral, so LCNF hands codegen a
    // `(ctor "Int.ofNat" ...)`/`(ctor "Int.negSucc" ...)` node. Discovered via
    // `c_int_guard_lt`/`c_int_guard_eq` (`if a < b then 1 else 0 : Int`),
    // which previously failed the whole compile-tests build with
    // `UnresolvedCall("Int.ofNat")`.
    let ir = r#"(module M (def f ((n Nat)) Int (ctor "Int.ofNat" n)))"#;
    assert_eq!(
        generate(ir),
        "pub fn f(n: u64) -> i64 {\n    ((n) as i64)\n}\n\n"
    );

    let ir = r#"(module M (def f ((n Nat)) Int (ctor "Int.negSucc" n)))"#;
    assert_eq!(
        generate(ir),
        "pub fn f(n: u64) -> i64 {\n    (-((n) as i64) - 1)\n}\n\n"
    );
}

#[test]
fn test_sized_arithmetic_wraps_and_is_infallible() {
    // Lean's UInt8.add is BitVec addition — wrapping IS the semantics, not a
    // failure. So sized definitions keep a plain return type.
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (add U8 a b)))"#;
    let out = generate(ir);
    assert!(out.contains("(a) as u8).wrapping_add(b)"), "got: {}", out);
    assert!(
        out.contains("-> u8 {"),
        "sized arithmetic must be infallible"
    );
    assert!(!out.contains("ComputeError"));
}

#[test]
fn test_sized_shift_masks_the_amount_mod_width() {
    // `UInt8.shiftLeft a b = ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩`
    // (`Init/Data/UInt/Basic.lean:126`) masks the amount mod the width — it
    // does NOT truncate to 0 past the width (that's `Nat.shiftRight`, whose
    // unbounded `Nat` genuinely has no width to mask by). So `1u8 << 8`
    // masks to `1u8 << 0 == 1`, and `checked_shl(..).unwrap_or(0)` — which
    // would give `0` here — is the WRONG rendering for sized shifts.
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (shl U8 a b)))"#;
    let out = generate(ir);
    assert!(out.contains("wrapping_shl"), "got: {}", out);
    assert!(!out.contains("checked_shl"), "checked_shl truncates to 0");
    assert!(!out.contains("unwrap_or(0)"));
}

#[test]
fn test_sized_division_is_total() {
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (div U8 a b)))"#;
    let out = generate(ir);
    assert!(out.contains("if (b) == 0 { 0 }"));
    assert!(!out.contains("ComputeError"));
}

#[test]
fn test_sized_pow_is_rejected_not_unsoundly_rendered() {
    // No sized `pow` row is whitelisted from Lean (`sizedOpSuffixes` has no
    // `pow`), but hand-written IR can still ask for one. `wrapping_pow`'s
    // exponent has no absorbing case the way shifts do, so the
    // `u32::try_from(..).unwrap_or(u32::MAX)` narrowing every other exponent
    // helper here uses would silently compute the wrong number for a `U64`
    // exponent that overflows `u32`. Rejected outright instead.
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (pow U8 a b)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}

#[test]
fn test_nat_to_int_widens() {
    let ir = r#"(module M (def f ((a Nat)) Int (convert Nat Int a)))"#;
    assert!(generate(ir).contains("((a) as i64)"));
}

#[test]
fn test_int_to_nat_clamps_negatives_to_zero() {
    // Lean's Int.toNat clamps: (-5).toNat = 0. `as u64` would wrap to a huge
    // number, which is the whole reason this needs a rendering rather than a
    // cast.
    let ir = r#"(module M (def f ((a Int)) Nat (convert Int Nat a)))"#;
    let out = generate(ir);
    assert!(out.contains("max(0)"), "got: {}", out);
    assert!(
        !out.contains("(a) as u64)."),
        "a bare cast would wrap negatives"
    );
}

#[test]
fn test_nat_to_sized_wraps() {
    let ir = r#"(module M (def f ((a Nat)) U8 (convert Nat U8 a)))"#;
    assert!(generate(ir).contains("as u8"));
}

#[test]
fn test_sized_to_nat_widens() {
    let ir = r#"(module M (def f ((a U8)) Nat (convert U8 Nat a)))"#;
    assert!(generate(ir).contains("as u64"));
}

#[test]
fn test_unsupported_conversion_is_rejected() {
    // Cross-width sized conversions are a deliberate non-goal.
    let ir = r#"(module M (def f ((a U8)) U32 (convert U8 U32 a)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}

#[test]
fn test_invariant_type_gets_private_fields_and_a_checked_constructor() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat))
    (invariant (and (le 1 q) (and (le 1 T) (le 1 O)))))
)
"#;
    let out = generate(ir);
    // Fields are pub(crate): generated code in this crate still constructs by
    // struct literal, because Lean already supplied the proof. Only external
    // callers are routed through the check.
    assert!(out.contains("pub(crate) q: u64"), "got: {}", out);
    assert!(!out.contains("pub q: u64"));
    assert!(out.contains("pub fn new(q: u64, T: u64, O: u64) -> Result<Self, crate::ComputeError>"));
    assert!(out.contains("if ((1 <= q) && ((1 <= T) && (1 <= O)))"));
    assert!(out.contains("crate::ComputeError::InvariantViolated(\"UorAtlas.Instance\")"));
    // One accessor per field, so external callers can still read.
    assert!(out.contains("pub fn q(&self) -> u64 { self.q }"));
    assert!(out.contains("pub fn T(&self) -> u64 { self.T }"));
}

#[test]
fn test_type_without_invariant_is_unchanged() {
    // The common case must not regress: public fields, no constructor, no
    // accessors.
    let ir = r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#;
    let out = generate(ir);
    assert!(out.contains("pub a: u64"));
    assert!(!out.contains("pub(crate)"));
    assert!(!out.contains("fn new("));
}

#[test]
fn test_connectives_render() {
    let ir = r#"
(module M
  (def f ((a Nat) (b Nat)) Bool (and (lt a b) (not (eq a b)))))
"#;
    assert!(generate(ir).contains("((a < b) && (!(a == b)))"));
}

#[test]
fn test_or_renders() {
    let ir = r#"(module M (def f ((a Nat) (b Nat)) Bool (or (lt a b) (eq a b))))"#;
    assert!(generate(ir).contains("((a < b) || (a == b))"));
}

#[test]
fn test_multi_constructor_type_with_an_invariant_is_rejected() {
    // A `Prop` field belongs to one constructor, so an invariant on a
    // multi-constructor type has no honest rendering: `new` would not know
    // which variant to build. Reject rather than render half of it.
    let ir = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat))
    (invariant (le 1 radius))))
"#;
    match generate_err(ir) {
        Error::UnsupportedFieldType(msg) => {
            assert!(msg.contains("M.Shape"), "got: {}", msg);
            assert!(msg.contains("2 constructors"), "got: {}", msg);
        }
        other => panic!("expected UnsupportedFieldType, got {:?}", other),
    }
}

#[test]
fn test_field_named_new_on_an_invariant_type_is_rejected() {
    // The accessors share an `impl` block with the generated `new`, so a field
    // named `new` would emit two inherent methods of that name (E0592).
    // `new` is not a Rust keyword, so nothing downstream escapes or renames it
    // — without this rejection the output simply would not compile.
    let ir = r#"
(module M
  (type "M.Collide"
    (ctor "M.Collide.mk" (new Nat) (other Nat))
    (invariant (le 1 new))))
"#;
    assert_eq!(
        generate_err(ir),
        Error::ReservedFieldName(String::from("M.Collide"), String::from("new"))
    );
}

#[test]
fn test_field_named_new_without_an_invariant_is_fine() {
    // The name is only reserved where the constructor exists. A type with no
    // invariant gets neither `new` nor accessors, so nothing collides.
    let ir = r#"(module M (type "M.Plain" (ctor "M.Plain.mk" (new Nat))))"#;
    assert!(generate(ir).contains("pub new: u64"));
}

#[test]
fn test_keyword_field_name_is_raw_escaped_inside_the_checked_constructor() {
    // `new`'s parameters, the struct's fields and the accessors all go through
    // `rust_ident`, so the invariant's references to those fields must too --
    // otherwise a field named `type` renders `pub fn new(r#type: u64)` whose
    // body reads `if (1 <= type)`, which is a syntax error.
    let ir = r#"
(module M
  (type "M.Kw"
    (ctor "M.Kw.mk" (type Nat) (fn Nat))
    (invariant (and (le 1 type) (le 1 fn)))))
"#;
    let out = generate(ir);
    assert!(
        out.contains("pub fn new(r#type: u64, r#fn: u64) -> Result<Self, crate::ComputeError>"),
        "got: {}",
        out
    );
    assert!(
        out.contains("if ((1 <= r#type) && (1 <= r#fn))"),
        "the invariant must escape the same names the parameters do; got: {}",
        out
    );
    assert!(out.contains("Ok(Kw { r#type, r#fn })"), "got: {}", out);
    assert!(out.contains("pub fn r#type(&self) -> u64 { self.r#type }"));
}

/// The rejections that changed their INTERNAL home at the cutover must arrive
/// here under the published name they had before it.
///
/// `test_every_error_variant_is_published_in_rejections` checks that every
/// variant *appears* in `REJECTIONS`; it cannot see a given input starting to
/// produce a different one. That is the property at risk when a rejection
/// moves from `prod-codegen`'s renderer into `prod-lower`, because
/// `From<LowerError>` is name-for-name and cannot recover a distinction the
/// lowering did not make.
#[test]
fn test_the_rehomed_rejections_keep_their_published_kind() {
    // Five list rejections. In `prod-lower` these are `UnsupportedList`, a
    // variant added for exactly this reason: they would otherwise have
    // arrived as `UnsupportedKind`, which is separately published.
    for ir in [
        r#"(module M (def g ((a Nat)) Nat a) (def m ((a Nat)) (List Nat) (call g a)))"#,
        r#"(module M (def m ((a Nat)) (List Nat) (add Nat a 1)))"#,
        r#"(module M (def m ((a Nat)) (List Nat) a))"#,
        r#"(module M (def m () (List Nat) (ctor "List.cons" (add Nat 1 2) (ctor "List.nil"))))"#,
        r#"(module M (def m ((a Nat)) Nat (ctor "List.cons" a (ctor "List.nil"))))"#,
    ] {
        assert!(
            matches!(generate_err(ir), Error::UnsupportedList(_)),
            "for {}: got {:?}",
            ir,
            generate_err(ir)
        );
    }

    // An unresolved callee and an opaque expression, in a body and inside an
    // invariant. Both used to be `prod-codegen`'s own named rejections and
    // both degraded when the lowering took them over.
    assert_eq!(
        generate_err(r#"(module M (def m ((a Nat)) Nat (extern "Foo.helper" a)))"#),
        Error::UnresolvedCall("Foo.helper".to_string())
    );
    assert_eq!(
        generate_err(r#"(module M (def m ((a Nat)) Nat (opaque "why")))"#),
        Error::OpaqueExpr("why".to_string())
    );
    assert_eq!(
        generate_err(
            r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat)) (invariant (extern "Foo.helper" q))))"#
        ),
        Error::UnresolvedCall("Foo.helper".to_string())
    );

    // A join point the lowering will not place, including the two shapes that
    // reach it only inside an invariant.
    assert!(matches!(
        generate_err(r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat)) (invariant (jmp g q))))"#),
        Error::UnsupportedJoinPoint(_)
    ));

    // A lazy connective whose right operand needs statements.
    assert!(matches!(
        generate_err(
            "(module M (def m ((a Nat) (b Nat)) Bool (and (lt a b) (lt (add Nat a b) b))))"
        ),
        Error::OpaqueExpr(_)
    ));
}

/// `generate_module` must call `lower_def_in`, not `lower_def`.
///
/// The table-free form cannot see the module's declarations, so it can check
/// neither a constructor's arity nor a projected field's existence -- two
/// rejections `REJECTIONS` still advertises. Both are pinned separately above;
/// this asserts the reason they still fire, by checking that the SAME IR is
/// accepted by the single-definition entry point, which documents having no
/// module to resolve against.
#[test]
fn test_generate_module_resolves_against_the_module_but_generate_def_cannot() {
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (alpha Nat)))
  (def f ((r (named "M.Rec"))) Nat (proj "M.Rec" "beta" r)))
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnknownField("M.Rec".to_string(), "beta".to_string())
    );

    let (_, module) = parse_module(ir).unwrap();
    // No module, so no declaration to disagree with -- and no `(named ...)`
    // to resolve either, which is the documented cost of the entry point.
    assert_eq!(
        generate_def(&module.definitions[0]),
        Err(Error::OpaqueType("M.Rec".to_string()))
    );
}
