use super::*;
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
    (add (mul (field inst "stride") h2)
         (add (mul (field inst "o") d) l)))

  (def belt ((inst (named "UorAtlas.Instance"))) Nat
    (mul (call class_count inst)
         (shl 1 (sub (field inst "o") 1))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n\npub fn classIndex(h2: u64, d: u64, l: u64, inst: crate::Instance) -> Result<u64, crate::ComputeError> {\n    Ok(((((inst.stride()) as u64).checked_mul(h2).ok_or(crate::ComputeError::MulOverflow)?) as u64).checked_add(((((inst.o) as u64).checked_mul(d).ok_or(crate::ComputeError::MulOverflow)?) as u64).checked_add(l).ok_or(crate::ComputeError::AddOverflow)?).ok_or(crate::ComputeError::AddOverflow)?)\n}\n\npub fn belt(inst: crate::Instance) -> Result<u64, crate::ComputeError> {\n    Ok(((class_count(inst)) as u64).checked_mul(((1) as u64).checked_shl(u32::try_from(((inst.o) as u64).saturating_sub(1)).map_err(|_| crate::ComputeError::ShiftExponentTooLarge)?).ok_or(crate::ComputeError::ShiftOverflow)?).ok_or(crate::ComputeError::MulOverflow)?)\n}\n\n"
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
        "pub fn f(x: u64) -> u64 {\n    match x {\n        Some(v) => v,\n        _ => 0,\n    }\n}\n\n"
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
      (alt "List.cons" (h t) (add h (call digitSum t)))))
  (def digits ((n Nat)) (List Nat)
    (if (lt n 8)
        (ctor "List.cons" n (ctor "List.nil"))
        (ctor "List.cons" (mod n 8) (call digits (div n 8)))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn digitSum(xs: &[u64]) -> Result<u64, crate::ComputeError> {\n    Ok(match xs {\n        [] => 0,\n        [h, t @ ..] => { let h = *h; ((h) as u64).checked_add(digitSum(t)?).ok_or(crate::ComputeError::AddOverflow)? },\n    })\n}\n\npub fn digits(n: u64, output: &mut [u64]) -> Result<usize, crate::ComputeError> {\n    if (n < 8) { match (output).split_first_mut() { None => Err(crate::ComputeError::OutputTooSmall), Some((__head0, __rest0)) => { *__head0 = n; let __len0 = Ok::<usize, crate::ComputeError>(0)?; Ok(__len0 + 1) } } } else { match (output).split_first_mut() { None => Err(crate::ComputeError::OutputTooSmall), Some((__head0, __rest0)) => { *__head0 = if (8) == 0 { 0 } else { (n) % (8) }; let __len0 = digits(if (8) == 0 { 0 } else { (n) / (8) }, __rest0)?; Ok(__len0 + 1) } } }\n}\n\n"
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
        (let _x_47 (proj "UorAtlas.Instance" "o" i)
          (if (lt n _x_47)
            (let _x_55 (ctor "List.nil") (let _x_56 (ctor "List.cons" n _x_55) _x_56))
            (let _x_50 (mod n _x_47)
              (let _x_51 (div n _x_47)
                (let _x_52 (call digits n_25 _x_51 i)
                  (let _x_53 (ctor "List.cons" _x_50 _x_52) _x_53)))))))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n\npub fn digits(fuel: u64, n: u64, i: crate::Instance, output: &mut [u64]) -> Result<usize, crate::ComputeError> {\n    match fuel {\n        0 => Ok::<usize, crate::ComputeError>(0),\n        _ => { let n_25 = (fuel).saturating_sub(1); { let _x_47 = (i).o; if (n < _x_47) { match (output).split_first_mut() { None => Err(crate::ComputeError::OutputTooSmall), Some((__head0, __rest0)) => { *__head0 = n; let __len0 = Ok::<usize, crate::ComputeError>(0)?; Ok(__len0 + 1) } } } else { { let _x_50 = if (_x_47) == 0 { 0 } else { (n) % (_x_47) }; { let _x_51 = if (_x_47) == 0 { 0 } else { (n) / (_x_47) }; match (output).split_first_mut() { None => Err(crate::ComputeError::OutputTooSmall), Some((__head0, __rest0)) => { *__head0 = _x_50; let __len0 = digits(n_25, _x_51, i, __rest0)?; Ok(__len0 + 1) } } } } } } },\n    }\n}\n\n"
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
  (def pure ((x Nat) (y Nat)) Nat (sub x y))
  (def viaDiv ((x Nat)) Nat (call pure (div x 2) 1))
  (def risky ((x Nat)) Nat (add x 1))
  (def caller ((x Nat)) Nat (call risky x))
  (def loops ((fuel Nat) (x Nat)) Nat
    (cases fuel
      (alt "Nat.zero" () x)
      (alt "Nat.succ" (k) (call loops k (add x 1)))))
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
    assert!(out.contains("loops(k, ((x) as u64).checked_add(1)"));
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
    assert_eq!(generate_err(ir), Error::HeapType("(Vec u64)".to_string()));
}

#[test]
fn test_computed_zero_arg_list_is_a_codegen_error() {
    // A golden whose elements are computed cannot be a promoted static slice.
    let ir = r#"
(module M
  (def g () (List Nat) (ctor "List.cons" (add 1 2) (ctor "List.nil")))
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
        "pub fn tryDecode(idx: u64) -> Option<u64> {\n    if (idx <= 96) { Some(idx) } else { None }\n}\n\npub fn fromOpt(x: Option<u64>) -> bool {\n    match x {\n        Some(v) => true,\n        None => false,\n    }\n}\n\n"
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
      (alt "Nat.succ" (k) (if (lt n 8) 1 (add 1 (call digitCount k (div n 8)))))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn digitCount(fuel: u64, n: u64) -> Result<u64, crate::ComputeError> {\n    Ok(match fuel {\n        0 => 0,\n        _ => { let k = (fuel).saturating_sub(1); if (n < 8) { 1 } else { ((1) as u64).checked_add(digitCount(k, if (8) == 0 { 0 } else { (n) / (8) })?).ok_or(crate::ComputeError::AddOverflow)? } },\n    })\n}\n\n"
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
    (let _x_4 (proj "UorAtlas.Instance" "t" i) (let _x_5 (proj "UorAtlas.Instance" "o" i) (let _x_13 (mul _x_4 _x_5) _x_13))))

  (def classDecode ((idx Nat) (i (named "UorAtlas.Instance"))) (Tuple Nat (Tuple Nat Nat))
    (let _x_4 (call stride i) (let h2 (div idx _x_4) (let rem (mod idx _x_4) (let _x_10 (proj "UorAtlas.Instance" "o" i) (let d (div rem _x_10) (let l (mod rem _x_10) (let _x_13 (ctor "Prod.mk" d l) (let _x_14 (ctor "Prod.mk" h2 _x_13) _x_14)))))))))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n\npub fn stride(i: crate::Instance) -> Result<u64, crate::ComputeError> {\n    Ok({ let _x_4 = (i).t; { let _x_5 = (i).o; { let _x_13 = ((_x_4) as u64).checked_mul(_x_5).ok_or(crate::ComputeError::MulOverflow)?; _x_13 } } })\n}\n\npub fn classDecode(idx: u64, i: crate::Instance) -> Result<(u64, (u64, u64)), crate::ComputeError> {\n    Ok({ let _x_4 = stride(i)?; { let h2 = if (_x_4) == 0 { 0 } else { (idx) / (_x_4) }; { let rem = if (_x_4) == 0 { 0 } else { (idx) % (_x_4) }; { let _x_10 = (i).o; { let d = if (_x_10) == 0 { 0 } else { (rem) / (_x_10) }; { let l = if (_x_10) == 0 { 0 } else { (rem) % (_x_10) }; { let _x_13 = (d, l); { let _x_14 = (h2, _x_13); _x_14 } } } } } } } })\n}\n\n"
    );
}

#[test]
fn test_generate_projection_on_unknown_type_uses_given_field_name() {
    // The type name carried on `proj` is documentation, not a lookup key:
    // codegen renders whatever field name it is given, regardless of
    // whether the type is otherwise known to it.
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (proj "Unknown.Struct" "count" (ctor "Unknown.Struct" x)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn f(x: u64) -> u64 {\n    (Unknown.Struct(x)).count\n}\n\n"
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
    (let g (jp g (a) (add a 1)) (jmp g x)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn f(x: u64) -> Result<u64, crate::ComputeError> {\n    Ok({ let g = /* jp \"g\" inlined at its jump site */ (); { let a = x; ((a) as u64).checked_add(1).ok_or(crate::ComputeError::AddOverflow)? } })\n}\n\n"
    );
}

#[test]
fn test_generate_cyclic_jp_skeleton() {
    let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (jp loop (i) (if (lt i 10) (jmp loop (add i 1)) i)))
)
"#;
    let out = generate(ir);
    assert!(out.contains("loop {"));
    assert!(out.contains("manual port required"));
}

#[test]
fn test_generate_pow() {
    let ir = r#"
(module M
  (def belt ((i Nat)) Nat
    (pow 2 (sub i 1)))
)
"#;
    let out = generate(ir);
    assert_eq!(
        out,
        "pub fn belt(i: u64) -> Result<u64, crate::ComputeError> {\n    Ok(((2) as u64).checked_pow(u32::try_from(((i) as u64).saturating_sub(1)).map_err(|_| crate::ComputeError::PowExponentTooLarge)?).ok_or(crate::ComputeError::PowOverflow)?)\n}\n\n"
    );
}

#[test]
fn test_generate_nat_arithmetic_policy_never_panics() {
    let ir = r#"
(module M
  (def add ((x Nat) (y Nat)) Nat (add x y))
  (def sub ((x Nat) (y Nat)) Nat (sub x y))
  (def div ((x Nat) (y Nat)) Nat (div x y))
  (def modu ((x Nat) (y Nat)) Nat (mod x y))
  (def shl ((x Nat) (y Nat)) Nat (shl x y))
  (def pow ((x Nat) (y Nat)) Nat (pow x y))
)
"#;
    let out = generate(ir);
    assert!(out.contains("checked_add(y).ok_or(crate::ComputeError::AddOverflow)?"));
    assert!(out.contains("saturating_sub(y)"));
    assert!(out.contains("if (y) == 0 { 0 } else { (x) / (y) }"));
    assert!(out.contains("if (y) == 0 { 0 } else { (x) % (y) }"));
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
    assert_eq!(out, "pub fn f(x: u64) -> u64 {\n    unreachable!()\n}\n\n");
}

#[test]
fn test_param_out_of_bounds_is_an_error() {
    let ir = "(module M (def f ((x Nat)) Nat (param 5)))";
    let (_, module) = parse_module(ir).unwrap();
    assert_eq!(generate_module(&module), Err(Error::ParamOutOfBounds(5)));
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
