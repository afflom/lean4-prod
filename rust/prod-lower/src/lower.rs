//! `Expr` -> [`crate::target`], for one definition.
//!
//! This is where a fallibility decision is *made*. Every printer downstream
//! reads the answer off the statement list rather than re-deriving it, which
//! is the whole point of the split: the same `Nat.add` becomes a
//! [`Stmt::TryLet`] under a profile whose `Nat` is a `u64` and a plain
//! [`TExpr::BinOp`] under one whose `Nat` is unbounded, and no backend gets a
//! vote.

use crate::error::LowerError;
use crate::names::{NameError, NamePolicy, NameTable};
use crate::profile::{DivisionSemantics, ListStrategy, TargetProfile};
use crate::shape::{Shape, Signatures};
use crate::target::{
    Arm, BinOp, Body, CtorDef, ErrorCode, FallibleOp, Lit, SeqQuery, Stmt, TExpr, TypeDef,
};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use prod_ir::{CtorDecl, Definition, Expr, Module, NumKind, Type, TypeDecl};

/// Lower one definition to its [`Body`], with no module around it.
///
/// Named types are therefore unresolvable: a constructor application, a match
/// alternative and a projection are all lowered without the declaration that
/// would say how many fields they have. Use [`lower_def_in`] when that matters
/// -- this entry point exists for the single-definition case, and mirrors
/// `prod_codegen::generate_def`'s documented behaviour exactly.
pub fn lower_def(
    def: &Definition,
    shapes: &Signatures,
    profile: &TargetProfile,
) -> Result<Body, LowerError> {
    lower_def_in(def, shapes, profile, &[])
}

/// Lower one definition to its [`Body`] against its module's type
/// declarations.
///
/// `decls` is the module's own [`TypeDecl`] list -- the *source* declarations,
/// not the lowered [`crate::target::TypeDef`]s. Every question it answers here
/// is about the IR rather than about any target: how many fields a constructor
/// has, and whether a projected field exists. Both are agreements the IR must
/// keep with itself.
pub fn lower_def_in(
    def: &Definition,
    shapes: &Signatures,
    profile: &TargetProfile,
    decls: &[TypeDecl],
) -> Result<Body, LowerError> {
    let shape = shapes
        .get(def.name.as_str())
        .copied()
        .unwrap_or(Shape::Value);
    check_signature(def, decls)?;
    let mut lowering = Lowering {
        params: &def.params,
        shapes,
        profile,
        next_temp: 0,
        reserved: bound_names(def),
        bound: def.params.iter().map(|(n, _)| n.clone()).collect(),
        scope: Vec::new(),
        types: Vec::new(),
        decls,
        jps: JpContext::collect(&def.body),
    };
    // The body is lowered in TAIL position: control flow is a statement here,
    // so each branch supplies its own terminator rather than yielding a value
    // for a `Return` this function appends.
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut env: Vec<ListBinding> = Vec::new();
    let output = match shape {
        // A list-shaped definition appends to a sequence instead of yielding
        // a value, so the first thing it needs is a name for that sequence.
        // It goes through `bind_source` like every other binder, so a
        // definition whose own source already writes `output` gets a fresh
        // name rather than two live bindings sharing one -- which
        // `prod-emit-rust`'s `uses()`, counting reads by name with no scope of
        // its own, would silently pool.
        Shape::Buffer | Shape::StaticList => {
            // `prod-codegen`'s own pre-check, kept DISTINCT from the
            // constant-cons-chain one below because it names a different
            // reason: this definition is shaped like a constant list but
            // computes its elements, and a promoted `&'static` slice holds
            // values, not work. Collapsing the two would report the wrong
            // cause for a definition that has this one.
            if shape == Shape::StaticList && crate::shape::is_fallible(&def.body, shapes, profile) {
                return Err(LowerError::UnsupportedList(format!(
                    "`{}` computes its list elements, so it cannot be a promoted &'static slice",
                    def.name
                )));
            }
            let seq = lowering.bind_source(OUTPUT_SEQUENCE);
            // Only a caller-supplied buffer can run out. A `NativeSequence`
            // host grows on demand, and a promoted `&'static` list has no
            // caller storage at all, so neither gets a bounds check.
            let bounded =
                shape == Shape::Buffer && profile.list_strategy == ListStrategy::CallerBuffer;
            lowering.flow(
                &def.body,
                Position::List { seq: &seq, bounded },
                &mut env,
                &mut stmts,
            )?;
            if shape == Shape::StaticList {
                check_constant_list(&stmts)?;
            }
            Some(seq)
        }
        Shape::Value | Shape::Fallible => {
            lowering.flow(&def.body, Position::Value, &mut env, &mut stmts)?;
            None
        }
    };
    Ok(Body {
        name: def.name.clone(),
        params: def.params.clone(),
        ret: def.ret.clone(),
        shape,
        output,
        stmts,
    })
}

/// Every type in a definition's signature must have a rendering, and a
/// `(named ...)` in one must be declared in this module.
///
/// The printers are total by construction, so nothing downstream can refuse a
/// signature: `prod-emit-rust`'s `value_type` renders an unrenderable type as
/// a placeholder identifier rather than an error. `prod-codegen` refused these
/// in `param_type_to_rust`/`type_to_rust`/`check_named_type`, before it
/// rendered the body, and the checks are in that order here so a signature
/// that trips several of them is still refused for the reason it is refused
/// today.
fn check_signature(def: &Definition, decls: &[TypeDecl]) -> Result<(), LowerError> {
    for (_, ty) in &def.params {
        check_signature_type(ty, decls)?;
    }
    check_signature_type(&def.ret, decls)
}

/// One signature type, checked in the order `prod-codegen` checked it.
///
/// **The order is load-bearing**, which is why it is one function rather than
/// two calls at each site. `check_named_type` ran first and recursed through
/// `Vec` and `List`, so `(Vec (named "Undeclared"))` reported the *undeclared
/// name* rather than the heap; `type_to_rust` ran second and stops at the
/// first unrenderable constructor. Both kinds are separately published, so
/// swapping them would change which one a caller sees for a type that trips
/// both.
fn check_signature_type(ty: &Type, decls: &[TypeDecl]) -> Result<(), LowerError> {
    check_named_types(ty, decls)?;
    // A top-level list borrows as a slice, so it is the ELEMENT type that has
    // to be renderable by value; nested any deeper, a list has no rendering at
    // all.
    match ty {
        Type::List(inner) => check_value_type(inner, decls),
        other => check_value_type(other, decls),
    }
}

/// Every `(named ...)` in a signature type, **at any depth**, must be declared
/// in this module -- inside `Option`, `List`, `Vec` or `Tuple` alike.
///
/// Deliberately blind to whether the surrounding type is renderable at all:
/// that is [`check_value_type`]'s question, asked afterwards. An undeclared
/// name is a disagreement inside the IR and outranks a type this tier cannot
/// hold.
fn check_named_types(ty: &Type, decls: &[TypeDecl]) -> Result<(), LowerError> {
    match ty {
        Type::Named(n) => {
            if decls.iter().any(|d| d.name == *n) {
                Ok(())
            } else {
                Err(LowerError::OpaqueType(n.clone()))
            }
        }
        Type::Option(inner) | Type::Vec(inner) | Type::List(inner) => {
            check_named_types(inner, decls)
        }
        Type::Tuple(items) => {
            for item in items {
                check_named_types(item, decls)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// A type in ordinary (owned, by-value) position.
///
/// The rejections and their wording are `prod-codegen`'s. The payloads name
/// the offending type in the **IR's** own spelling rather than any target's:
/// this crate is the language-neutral half of the split, and a Rust type name
/// in a diagnostic here would be exactly the backend knowledge the seam
/// exists to keep out.
fn check_value_type(ty: &Type, decls: &[TypeDecl]) -> Result<(), LowerError> {
    match ty {
        Type::Named(n) => {
            if decls.iter().any(|d| d.name == *n) {
                Ok(())
            } else {
                Err(LowerError::OpaqueType(n.clone()))
            }
        }
        Type::Option(inner) => check_value_type(inner, decls),
        Type::Tuple(items) => {
            for item in items {
                check_value_type(item, decls)?;
            }
            Ok(())
        }
        Type::Opaque(what) => Err(LowerError::OpaqueType(what.clone())),
        Type::List(inner) => Err(LowerError::UnsupportedList(format!(
            "(List {}) is only supported directly as a parameter or return type",
            describe_type(inner)
        ))),
        Type::Vec(inner) => Err(LowerError::HeapType(format!(
            "(Vec {})",
            describe_type(inner)
        ))),
        _ => Ok(()),
    }
}

/// A type in the IR's own surface syntax, for a diagnostic payload.
fn describe_type(ty: &Type) -> String {
    match ty {
        Type::Nat => String::from("Nat"),
        Type::Int => String::from("Int"),
        Type::Bool => String::from("Bool"),
        Type::UInt(k) => match k {
            NumKind::U8 => String::from("U8"),
            NumKind::U16 => String::from("U16"),
            NumKind::U32 => String::from("U32"),
            NumKind::U64 => String::from("U64"),
            NumKind::Nat => String::from("Nat"),
            NumKind::Int => String::from("Int"),
        },
        Type::Named(n) => format!("(named {:?})", n),
        Type::Opaque(n) => format!("(opaque {:?})", n),
        Type::Option(inner) => format!("(Option {})", describe_type(inner)),
        Type::List(inner) => format!("(List {})", describe_type(inner)),
        Type::Vec(inner) => format!("(Vec {})", describe_type(inner)),
        Type::Tuple(items) => {
            let mut out = String::from("(Tuple");
            for item in items {
                out.push(' ');
                out.push_str(&describe_type(item));
            }
            out.push(')');
            out
        }
    }
}

/// The source name a list-shaped definition's output sequence asks for.
///
/// A *request*, not a guarantee: it goes through `bind_source` like any other
/// binder, so a definition that already binds `output` gets something else.
const OUTPUT_SEQUENCE: &str = "output";

/// A promoted `&'static [E]` has to be a constant run of elements and nothing
/// else, because that is all an array literal can hold.
///
/// Expressed as a check on the *lowered* statements rather than on the source
/// expression: a computed element leaves a [`Stmt::TryLet`] in front of its
/// `Push`, and a branch leaves an `If` or a `Switch`, so one shape test
/// catches every way a zero-argument list definition can fail to be constant.
/// `prod-codegen` rejects the same set, and the message is its own.
fn check_constant_list(stmts: &[Stmt]) -> Result<(), LowerError> {
    let constant = match stmts.split_last() {
        Some((Stmt::Return(_), pushes)) => pushes.iter().all(|s| matches!(s, Stmt::Push { .. })),
        _ => false,
    };
    if constant {
        Ok(())
    } else {
        Err(LowerError::UnsupportedList(String::from(
            "zero-argument list definitions must be constant cons chains",
        )))
    }
}

/// Lower every type declaration in `module`.
///
/// This is the *decision* half of what `prod-codegen`'s `generate_type_decl`
/// used to do in one piece. Whether a type is representable at all, whether
/// its fields are private, whether it has an invariant and what predicate that
/// invariant is, whether a field name is already taken by the generated
/// checked constructor -- all settled here. How any of it is spelled is the
/// printer's, and `emit_types` returns a `String` rather than a `Result`
/// precisely because nothing is left for it to refuse.
pub fn lower_types(module: &Module, policy: &NamePolicy) -> Result<Vec<TypeDef>, LowerError> {
    check_type_name_collisions(&module.types, policy)?;
    let mut out = Vec::with_capacity(module.types.len());
    for decl in &module.types {
        out.push(lower_type_decl(decl, &module.types, policy)?);
    }
    Ok(out)
}

/// Two Lean types whose last name components collide once mangled: this is
/// the one implementation of that check, sourced from [`NameTable`] rather
/// than re-derived, so the names that are certified injective are the names
/// that actually get emitted.
///
/// Deliberately scoped to types only, with every type's constructors and
/// fields stripped before the table is built. `NameTable::build` also checks
/// constructor and field injectivity, but folding that in here would reject
/// modules under a `DuplicateTypeName` message naming the wrong kind of
/// collision -- practically every Lean structure names its constructor `mk`.
fn check_type_name_collisions(types: &[TypeDecl], policy: &NamePolicy) -> Result<(), LowerError> {
    let types_only = Module {
        name: String::new(),
        types: types
            .iter()
            .map(|decl| TypeDecl {
                name: decl.name.clone(),
                ctors: Vec::new(),
                unsupported: None,
                invariant: None,
            })
            .collect(),
        definitions: Vec::new(),
    };
    match NameTable::build(&types_only, policy) {
        Ok(_) => Ok(()),
        Err(NameError::Collision { target, .. }) => Err(LowerError::DuplicateTypeName(target)),
    }
}

/// Lower one type declaration.
///
/// The order of the checks is `prod-codegen`'s order, deliberately: a
/// declaration that trips several of them must still be rejected for the same
/// reason it is rejected today, and the rejection wording is pinned by the
/// published subset contract.
fn lower_type_decl(
    decl: &TypeDecl,
    all: &[TypeDecl],
    policy: &NamePolicy,
) -> Result<TypeDef, LowerError> {
    // The exporter reached this type but could not describe it. It is declared
    // anyway so that the rejection names a reason instead of an unknown type.
    if let Some(reason) = &decl.unsupported {
        return Err(match reason.as_str() {
            "type parameters" => LowerError::PolymorphicType(decl.name.clone()),
            "recursive" => LowerError::RecursiveType(decl.name.clone()),
            other => LowerError::OpaqueType(format!("{} ({})", decl.name, other)),
        });
    }
    for ctor in &decl.ctors {
        for (field, ty) in &ctor.fields {
            check_field_type(ty, &decl.name, field, all)?;
        }
    }

    if decl.ctors.len() == 1 {
        let ctor = &decl.ctors[0];
        let fields = lower_fields(ctor, policy)?;

        let invariant = match &decl.invariant {
            None => None,
            Some(predicate) => {
                // The accessors and the checked constructor are members of the
                // same type, so a field named `new` would produce two members
                // of that name. `new` is not a keyword in any policy's list,
                // so the mangling leaves it alone and nothing downstream would
                // catch it -- the output would simply not compile. Reject
                // here, naming the type and the field.
                for (name, _) in &ctor.fields {
                    if policy.apply(name) == CHECKED_CONSTRUCTOR {
                        return Err(LowerError::ReservedFieldName(
                            decl.name.clone(),
                            name.clone(),
                        ));
                    }
                }
                Some(lower_invariant(
                    predicate, &decl.name, &fields, all, policy,
                )?)
            }
        };

        return Ok(TypeDef {
            name: policy.apply(&decl.name),
            lean_name: decl.name.clone(),
            ctors: alloc::vec![CtorDef {
                name: policy.apply(&ctor.name),
                lean_name: ctor.name.clone(),
                fields,
            }],
            fields_private: invariant.is_some(),
            invariant,
        });
    }

    // Only a single-constructor structure can carry an invariant: a `Prop`
    // field belongs to one constructor. Reject rather than render half of it.
    if decl.invariant.is_some() {
        return Err(LowerError::UnsupportedFieldType(format!(
            "`{}` carries an invariant but has {} constructors; only a \
             single-constructor structure can have one",
            decl.name,
            decl.ctors.len()
        )));
    }

    let mut ctors = Vec::with_capacity(decl.ctors.len());
    for ctor in &decl.ctors {
        ctors.push(CtorDef {
            name: policy.apply(&ctor.name),
            lean_name: ctor.name.clone(),
            fields: lower_fields(ctor, policy)?,
        });
    }
    Ok(TypeDef {
        name: policy.apply(&decl.name),
        lean_name: decl.name.clone(),
        ctors,
        invariant: None,
        fields_private: false,
    })
}

/// The name of the generated checked constructor, in the Target IR's own
/// vocabulary. A printer that spells it differently owes the corresponding
/// reservation in its own policy; the decision that *some* member name is
/// taken belongs here, with the decision to generate the member at all.
const CHECKED_CONSTRUCTOR: &str = "new";

/// A constructor's fields under the caller's naming policy, rejecting any
/// whose type has no representation at all.
///
/// Separate from [`check_field_type`] and run after it, because
/// `prod-codegen` runs the two in that order: a field type can be
/// unrepresentable (`Opaque`) *and* recursive, and the reason reported has to
/// stay the one reported today.
fn lower_fields(ctor: &CtorDecl, policy: &NamePolicy) -> Result<Vec<(String, Type)>, LowerError> {
    let mut fields = Vec::with_capacity(ctor.fields.len());
    for (name, ty) in &ctor.fields {
        check_representable(ty)?;
        fields.push((policy.apply(name), ty.clone()));
    }
    Ok(fields)
}

/// A field type must be renderable and must not make the type recursive.
///
/// `owner` and `field` are the Lean constant and field name responsible, and
/// they appear in the rejection message: a failure has to name the declaration
/// that caused it, and "a list field would need owned storage" on its own
/// leaves the reader to grep for which one.
fn check_field_type(
    ty: &Type,
    owner: &str,
    field: &str,
    all: &[TypeDecl],
) -> Result<(), LowerError> {
    match ty {
        Type::Named(n) => {
            if n == owner {
                return Err(LowerError::RecursiveType(String::from(owner)));
            }
            match all.iter().find(|d| d.name == *n) {
                // One level of indirection is enough to catch the mutual case
                // too: B referring back to A makes A reachable from A.
                Some(other) => {
                    for ctor in &other.ctors {
                        for (_, inner) in &ctor.fields {
                            if let Type::Named(m) = inner {
                                if m == owner {
                                    return Err(LowerError::RecursiveType(String::from(owner)));
                                }
                            }
                        }
                    }
                    Ok(())
                }
                None => Err(LowerError::OpaqueType(n.clone())),
            }
        }
        // A sequence field would need owned storage, which the allocation-free
        // tier does not have. Lists are supported as borrowed parameters and
        // caller-owned output buffers only, never as owned struct fields.
        Type::List(_) => Err(LowerError::UnsupportedFieldType(format!(
            "`{}.{}`: a list field would need owned storage",
            owner, field
        ))),
        Type::Vec(_) => Err(LowerError::UnsupportedFieldType(format!(
            "`{}.{}`: a vector field would need heap storage",
            owner, field
        ))),
        Type::Tuple(items) => {
            for item in items {
                check_field_type(item, owner, field, all)?;
            }
            Ok(())
        }
        Type::Option(inner) => check_field_type(inner, owner, field, all),
        _ => Ok(()),
    }
}

/// A type the printers have no rendering for at all. `List` and `Vec` are
/// already gone by the time this runs; what is left is `Opaque`, the type the
/// exporter emits when it gave up.
fn check_representable(ty: &Type) -> Result<(), LowerError> {
    match ty {
        Type::Opaque(s) => Err(LowerError::OpaqueType(s.clone())),
        Type::Option(inner) => check_representable(inner),
        Type::Tuple(items) => {
            for item in items {
                check_representable(item)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Lower a structure's invariant: a predicate over the structure's own fields.
///
/// Deliberately **not** [`Lowering::expr`]. That one needs a
/// [`TargetProfile`] to decide what can fail, and `lower_types` has none --
/// which is the right shape rather than an inconvenience. `lower_types`
/// produces one [`TypeDef`] that *every* backend prints, so the predicate in
/// it has to be a single total expression under every profile at once. That
/// is what [`TargetProfile::op_is_fallible_under_any_profile`] answers.
/// (One thing escapes that question: a `Call`, whose shape needs a
/// [`Signatures`] map `lower_types` does not have. See its arm below -- the
/// assumption is `prod-codegen`'s own, preserved rather than invented.)
///
/// What is accepted is therefore the whole **total** fragment, not merely the
/// boolean one: `Nat` subtraction saturates, sized arithmetic wraps, `Nat`
/// shift-right truncates, and unsigned division is total -- all of which
/// the renderer this replaced rendered inside a checked constructor, as a
/// single expression with no `?` in it. Refusing them would narrow the published
/// subset for a shape (`1 <= q - T`) that is entirely plausible in a
/// Lean-proved structure.
///
/// What is refused, and this is a **deliberate divergence** from
/// `prod-codegen` rather than a deferral:
///
/// * An operation that can fail. The renderer this replaced did render it --
///   `new` returns a `Result`, so `checked_mul(..)?` compiled -- but the
///   result is a checked constructor that reports `MulOverflow` when the thing that
///   actually failed was the invariant it was checking. Refusing to generate
///   the type is the better answer, and it gets a named rejection saying so.
/// * A node with no total-expression form in the Target IR at all: `If`,
///   `Let` and `Match` are statements here, and so are `Jp`/`Jmp`. Those are
///   [`LowerError::OpaqueExpr`] and [`LowerError::UnsupportedJoinPoint`],
///   which is what they are. None can appear in a Lean-exported invariant:
///   `lowerProp` and the invariant fold in `lean/Prod/Lower.lean` emit
///   comparisons, connectives, arithmetic and projections and nothing else.
///
/// Field references resolve to the *target* field identifiers, so the
/// predicate reads the same names the fields and the constructor parameters
/// are declared with. Without that, a field named `type` would be declared
/// escaped and read raw.
///
/// The operand order is preserved exactly. `q >= 1` reaches here as
/// `le 1 q` and must stay `1 <= q`: a reversed comparison still compiles,
/// still returns a `bool`, and rejects precisely the inputs it should accept.
fn lower_invariant(
    e: &Expr,
    owner: &str,
    fields: &[(String, Type)],
    decls: &[TypeDecl],
    policy: &NamePolicy,
) -> Result<TExpr, LowerError> {
    let sub = |x: &Expr| lower_invariant(x, owner, fields, decls, policy);
    match e {
        Expr::Nat(n) => Ok(TExpr::Lit(Lit::Nat(*n))),
        Expr::Int(n) => Ok(TExpr::Lit(Lit::Int(*n))),
        Expr::Bool(b) => Ok(TExpr::Lit(Lit::Bool(*b))),
        Expr::Var(name) => Ok(TExpr::Var(policy.apply(name))),

        // The field's declared type is what a bare `Var` is read at here; in
        // a definition body the same question is answered by the binder
        // table. That is the whole difference between the two paths, so it is
        // the only thing passed in.
        Expr::Eq(a, b) => Ok(compare(BinOp::Eq, sub(a)?, sub(b)?, &field_kind(fields))),
        Expr::Lt(a, b) => Ok(compare(BinOp::Lt, sub(a)?, sub(b)?, &field_kind(fields))),
        Expr::Le(a, b) => Ok(compare(BinOp::Le, sub(a)?, sub(b)?, &field_kind(fields))),
        Expr::Gt(a, b) => Ok(compare(BinOp::Gt, sub(a)?, sub(b)?, &field_kind(fields))),

        // Total under every profile -- `Int.toNat` clamps and `Nat.toUIntN`
        // truncates, and neither is a failure -- so a conversion is admitted
        // in an invariant on exactly the terms the body path admits it, and
        // through the same whitelist.
        Expr::Convert(from, to, a) => {
            check_conversion(*from, *to)?;
            Ok(TExpr::Convert(*from, *to, Box::new(sub(a)?)))
        }

        Expr::And(a, b) => Ok(TExpr::And(Box::new(sub(a)?), Box::new(sub(b)?))),
        Expr::Or(a, b) => Ok(TExpr::Or(Box::new(sub(a)?), Box::new(sub(b)?))),
        Expr::Not(a) => Ok(TExpr::Not(Box::new(sub(a)?))),

        Expr::Add(k, a, b) => invariant_arith(e, owner, *k, BinOp::Add, sub(a)?, sub(b)?),
        Expr::Sub(k, a, b) => invariant_arith(e, owner, *k, BinOp::Sub, sub(a)?, sub(b)?),
        Expr::Mul(k, a, b) => invariant_arith(e, owner, *k, BinOp::Mul, sub(a)?, sub(b)?),
        // `Nat` and the sized kinds are unsigned, where truncating, flooring
        // and Euclidean division coincide, so no host needs a correction and
        // the operator is the same for every profile. `Int` division is
        // fallible under every profile and is rejected below before the
        // question of which operator arises.
        Expr::Div(k, a, b) => invariant_arith(e, owner, *k, BinOp::Div, sub(a)?, sub(b)?),
        Expr::Mod(k, a, b) => invariant_arith(e, owner, *k, BinOp::Mod, sub(a)?, sub(b)?),
        Expr::Shl(k, a, b) => {
            reject_int_shift(*k)?;
            invariant_arith(e, owner, *k, BinOp::Shl, sub(a)?, sub(b)?)
        }
        Expr::Shr(k, a, b) => {
            reject_int_shift(*k)?;
            invariant_arith(e, owner, *k, BinOp::Shr, sub(a)?, sub(b)?)
        }
        Expr::Pow(k, a, b) => {
            reject_sized_pow(*k)?;
            invariant_arith(e, owner, *k, BinOp::Pow, sub(a)?, sub(b)?)
        }
        Expr::Neg(k, a) => {
            reject_non_int_neg(*k)?;
            let _ = sub(a)?;
            // `Int` negation is fallible under every profile, so this is
            // always the rejection; it is spelled through the same helper so
            // there is one message for "an invariant may not fail".
            Err(invariant_can_fail(owner, e))
        }

        // A call with no [`Signatures`] to consult, exactly as
        // `generate_type_decl` renders one: it builds its `Renderer` with an
        // empty signature map, so an invariant's callee is assumed total and
        // gets no `?`. The assumption is preserved rather than fixed here --
        // fixing it means giving `lower_types` the module's signatures, which
        // is a signature change this task does not own.
        Expr::Call(name, args) => {
            let mut lowered = Vec::with_capacity(args.len());
            for arg in args {
                lowered.push(sub(arg)?);
            }
            Ok(TExpr::Call(name.clone(), lowered))
        }

        // The same check the body path makes, through the same function.
        // Passing a projection through unchecked would put `(q).nope` in the
        // generated `new` -- output that does not compile -- where
        // `prod-codegen`, whose invariant renderer is built with the module's
        // type table, reports `UnknownField`.
        //
        // The field is checked BEFORE the operand is lowered, because the
        // rejection KIND is published: for `(proj "M.S" "nope" (opaque "x"))`
        // the renderer this replaced reported `UnknownField`, and lowering the
        // operand first would report `OpaqueExpr` instead. Both are refusals;
        // only one is the one the contract names.
        Expr::Proj(ty, field, value) => {
            check_projected_field(decls, ty, field)?;
            let value = sub(value)?;
            Ok(TExpr::Proj(ty.clone(), field.clone(), Box::new(value)))
        }

        // An invariant has no parameters -- it is a predicate over fields --
        // so every parameter index is out of bounds. `prod-codegen` builds its
        // invariant renderer with `params: &[]` and reports exactly this.
        Expr::Param(index) => Err(LowerError::ParamOutOfBounds(*index)),

        // A constructor application in an invariant. The renderer this
        // replaced rendered one -- its invariant renderer was the same
        // renderer as everywhere else -- so refusing here would have narrowed
        // the published subset at the cutover. Admitted on the same terms the
        // body path admits it, through the same arity and resolvability
        // checks.
        Expr::Ctor(name, args) => {
            let mut lowered = Vec::with_capacity(args.len());
            for arg in args {
                lowered.push(sub(arg)?);
            }
            ctor_expr(decls, name, lowered)
        }

        // The exporter reached a construct it could not describe, and a call
        // it could not resolve. Both had names in `prod-codegen`; they keep
        // them rather than degrading into a generic refusal.
        Expr::Opaque(what) => Err(LowerError::OpaqueExpr(what.clone())),
        Expr::Extern(name, _) => Err(LowerError::UnresolvedCall(name.clone())),

        // Control flow inside an invariant. `Jp` and `Jmp` are join points,
        // and this lowering places none in a predicate that has no statement
        // list to place them into. The renderer this replaced rendered them,
        // so this is a DIVERGENCE, in the safe direction. Neither can appear in a
        // Lean-exported invariant: `lowerProp` and the invariant fold in
        // `lean/Prod/Lower.lean` emit comparisons, connectives, arithmetic
        // and projections, and nothing that introduces a join point.
        Expr::Jp { name, .. } | Expr::Jmp(name, _) => {
            Err(LowerError::UnsupportedJoinPoint(name.clone()))
        }

        // `If`, `Let`, `Match` and `Unreachable`: statements in this IR, and
        // an invariant is one total expression with no statement list around
        // it.
        other => Err(LowerError::OpaqueExpr(format!(
            "{} in `{}`'s invariant",
            node_name(other),
            owner
        ))),
    }
}

/// A constructor application, resolved against the module's declarations.
///
/// One implementation for the body path and the invariant path, because the
/// two questions -- does the arity agree with the declaration, and is the name
/// something a target can spell at all -- are the same question in both.
///
/// A dotted name with no declaration is REFUSED rather than passed to a
/// printer: a Lean name is not a Rust path in expression position
/// (`Conformance.NoProp.mk(n, n)` parses as field access on a value called
/// `Conformance`), so it would surface as a compiler error far from the IR
/// that caused it. A dot-free name is at least a syntactically valid path to
/// a type the host may supply by hand, so it passes through -- exactly
/// `prod-codegen`'s split.
fn ctor_expr(decls: &[TypeDecl], name: &str, args: Vec<TExpr>) -> Result<TExpr, LowerError> {
    match ctor_decl(decls, name) {
        Some((_, cdecl)) => {
            // Arity is an agreement between the declaration and this use, so
            // a disagreement is the IR contradicting itself. Rendering it
            // would emit a call with the wrong number of arguments.
            if args.len() != cdecl.fields.len() {
                return Err(LowerError::UnsupportedFieldType(format!(
                    "`{}` takes {} field(s) but got {} argument(s)",
                    name,
                    cdecl.fields.len(),
                    args.len()
                )));
            }
            Ok(TExpr::Ctor(String::from(name), args))
        }
        None if is_builtin_ctor(name, args.len()) => Ok(TExpr::Ctor(String::from(name), args)),
        None if name.contains('.') => Err(LowerError::UnresolvedCall(String::from(name))),
        None => Ok(TExpr::Ctor(String::from(name), args)),
    }
}

/// The constructors every backend knows without a declaration: Lean's own
/// `Bool`, `Option`, `Prod` and `Int`.
///
/// Named here rather than in a printer because whether one is *admitted* is a
/// question about the source language -- `prod-codegen` answered it in exactly
/// this list -- while how each is spelled is the printer's business. The
/// arities are part of the answer: `Option.some` with two arguments is not
/// Lean's `Option.some`.
fn is_builtin_ctor(name: &str, arity: usize) -> bool {
    matches!(
        (name, arity),
        ("Prod.mk", _)
            | ("Bool.true", 0)
            | ("Bool.false", 0)
            | ("Option.none", 0)
            | ("Option.some", 1)
            | ("Int.ofNat", 1)
            | ("Int.negSucc", 1)
    )
}

/// One arithmetic node inside an invariant: total, or a named rejection.
fn invariant_arith(
    node: &Expr,
    owner: &str,
    kind: NumKind,
    op: BinOp,
    a: TExpr,
    b: TExpr,
) -> Result<TExpr, LowerError> {
    if TargetProfile::op_is_fallible_under_any_profile(node) {
        return Err(invariant_can_fail(owner, node));
    }
    Ok(TExpr::BinOp(kind, op, Box::new(a), Box::new(b)))
}

/// The rejection for an invariant that contains a failing operation.
///
/// The renderer this replaced rendered this rather than refusing it, and the
/// divergence is deliberate: the generated `new` would report the
/// *arithmetic's* error --
/// `MulOverflow` -- for a caller whose actual mistake was violating the
/// invariant. A checked constructor that misattributes its own failure is
/// worse than a type that is not generated at all.
fn invariant_can_fail(owner: &str, node: &Expr) -> LowerError {
    LowerError::UnsupportedFieldType(format!(
        "`{}`: an invariant may not contain an operation that can fail, and `{}` can; \
         the checked constructor would report that failure instead of the invariant \
         it was checking",
        owner,
        node_name(node)
    ))
}

/// A comparison over two lowered operands, at the kind its operands are read
/// at.
///
/// One implementation, called from the definition-body path and the invariant
/// path. They answer "what kind is this variable" from different tables -- a
/// field list there, the binder table here -- so that question, and only that
/// question, is the parameter. Task 5 found three divergences between those
/// two paths; this is the shape that stops a fourth.
///
/// The operand order is preserved exactly: `Lt(a, b)` is `a < b`. A reversed
/// comparison still compiles, still returns a `bool`, and rejects precisely
/// the inputs it should accept.
fn compare(op: BinOp, a: TExpr, b: TExpr, var_kind: &dyn Fn(&str) -> Option<NumKind>) -> TExpr {
    let kind = compare_kind(&a, &b, var_kind);
    TExpr::BinOp(kind, op, Box::new(a), Box::new(b))
}

/// The invariant path's answer to "what kind is this variable": a structure's
/// own field, at its declared type.
fn field_kind(fields: &[(String, Type)]) -> impl Fn(&str) -> Option<NumKind> + '_ {
    move |name: &str| {
        fields
            .iter()
            .find(|(f, _)| f == name)
            .and_then(|(_, ty)| type_kind(ty))
    }
}

/// The conversions that have a rendering: the LOSSLESS set, and nothing else.
///
/// One implementation, called from the definition-body path and the invariant
/// path, and `prod-codegen`'s own set unchanged. Every sized-to-sized pair
/// (`UInt8 -> UInt32` included) and every `Int`-to-sized pair is a deliberate
/// non-goal: a printer that quietly emitted `as u32` for one of them would
/// change the number, so the refusal lives here, where the semantics are,
/// rather than in three printers that each have to remember it.
fn check_conversion(from: NumKind, to: NumKind) -> Result<(), LowerError> {
    use NumKind::*;
    match (from, to) {
        // `Nat -> Int` widens; `Int -> Nat` is Lean's `Int.toNat`, which
        // clamps negatives to zero rather than failing.
        (Nat, Int) | (Int, Nat) => Ok(()),
        // `Nat.toUIntN` truncates, matching `BitVec`; `UIntN.toNat` widens.
        (Nat, U8) | (Nat, U16) | (Nat, U32) | (Nat, U64) => Ok(()),
        (U8, Nat) | (U16, Nat) | (U32, Nat) | (U64, Nat) => Ok(()),
        _ => Err(LowerError::UnsupportedKind(format!(
            "no conversion from {:?} to {:?}; cross-width sized conversions are a deliberate non-goal",
            from, to
        ))),
    }
}

/// The numeric kind a comparison's operands are read at.
///
/// An operand with a kind of its own settles it: a field reference has a
/// declared type, and an arithmetic node carries its kind. A bare literal does
/// not, so it is consulted only when neither side is more specific. `le 1 used`
/// over a `UInt8` field is a `UInt8` comparison, not a `Nat` one, even though
/// the literal on the left says nothing.
fn compare_kind(a: &TExpr, b: &TExpr, var_kind: &dyn Fn(&str) -> Option<NumKind>) -> NumKind {
    for operand in [a, b] {
        if let Some(kind) = operand_kind(operand, var_kind) {
            return kind;
        }
    }
    for operand in [a, b] {
        if let TExpr::Lit(Lit::Int(_)) = operand {
            return NumKind::Int;
        }
    }
    NumKind::Nat
}

fn operand_kind(e: &TExpr, var_kind: &dyn Fn(&str) -> Option<NumKind>) -> Option<NumKind> {
    match e {
        TExpr::Var(name) => var_kind(name),
        TExpr::BinOp(kind, op, ..) => match op {
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt => None,
            _ => Some(*kind),
        },
        // A conversion says what kind it produces, which is the whole reason
        // it is written: `(convert Nat U8 x) < cap` is a `UInt8` comparison.
        TExpr::Convert(_, to, _) => Some(*to),
        // Every question about a sequence answers with a count.
        TExpr::Seq(..) => Some(NumKind::Nat),
        _ => None,
    }
}

fn type_kind(ty: &Type) -> Option<NumKind> {
    match ty {
        Type::Nat => Some(NumKind::Nat),
        Type::Int => Some(NumKind::Int),
        Type::UInt(k) => Some(*k),
        _ => None,
    }
}

/// A projection must name a field its declared type actually has.
///
/// One implementation, called from both the definition-body path and the
/// invariant path. They diverged once -- the invariant path passed
/// projections through unchecked and emitted `(q).nope` -- so the check lives
/// in one place where a future caller inherits it rather than having to
/// remember it.
///
/// A type this module does not declare is not checked, because there is
/// nothing to check it against; that is `prod-codegen`'s behaviour too.
fn check_projected_field(decls: &[TypeDecl], ty: &str, field: &str) -> Result<(), LowerError> {
    let Some(decl) = decls.iter().find(|d| d.name == *ty) else {
        return Ok(());
    };
    let declared = decl
        .ctors
        .iter()
        .any(|c| c.fields.iter().any(|(name, _)| name == field));
    if declared {
        Ok(())
    } else {
        Err(LowerError::UnknownField(
            String::from(ty),
            String::from(field),
        ))
    }
}

/// The declaration of a constructor, by its full Lean name.
fn ctor_decl<'m>(decls: &'m [TypeDecl], name: &str) -> Option<(&'m TypeDecl, &'m CtorDecl)> {
    decls.iter().find_map(|decl| {
        decl.ctors
            .iter()
            .find(|c| c.name == name)
            .map(|c| (decl, c))
    })
}

/// Which of Lean's two total-but-differently-zero integer operations is being
/// lowered. They share a divisor-is-zero guard but not its value.
#[derive(Clone, Copy)]
enum DivMod {
    Div,
    Mod,
}

/// A `let`-bound list value, deferred to the point where the list is
/// consumed.
///
/// A list `let` binds nothing at runtime: the elements go into the output
/// sequence where the list is *used*, not where it is named, so the bound
/// expression is re-lowered at each consumption site.
struct ListBinding<'a> {
    /// The source name the `let` bound.
    name: String,
    /// The expression it was bound to.
    value: &'a Expr,
    /// `Lowering::scope.len()` at the point the `let` was WRITTEN.
    ///
    /// Re-lowering happens somewhere else in the traversal, where `scope` may
    /// have grown binders the bound expression cannot see. A `Var` inside it
    /// has to resolve the way it would have resolved where it was written --
    /// which is the whole reason `bind_source`/`scope` exist, and the
    /// assumption ("LCNF names every binder uniquely") this used to rely on
    /// instead is precisely the one the uniquification fix refused to make.
    scope: usize,
}

/// What the lowering does with what an expression in tail position produces.
///
/// The two positions share every control-flow lowering and differ only at the
/// leaves, which is why they are a parameter rather than two functions.
#[derive(Clone, Copy)]
enum Position<'p> {
    /// Return it.
    Value,
    /// Append it to the named output sequence.
    List {
        seq: &'p str,
        /// Is the sequence a caller-supplied buffer that can run out?
        ///
        /// True only for [`crate::profile::ListStrategy::CallerBuffer`] on a
        /// `Shape::Buffer` definition. A `NativeSequence` host grows on
        /// demand, and a promoted `&'static` list has no caller storage, so
        /// neither has a bound to check against.
        bounded: bool,
    },
}

/// Lowering makes every binder in a [`Body`] unique, because the Target IR has
/// no nested scope to rely on.
///
/// `Expr::Let` is an *expression* -- it can sit in an operand -- and the
/// statement list it lowers into is flat, so its `Stmt::Let` lands in the
/// enclosing list and stays live for everything after it. Lean's scoping said
/// otherwise. In `Add(Let("x", 1, Var("x")), Var("x"))` over a parameter `x`,
/// the second operand means the *parameter*; flattened naively it would read
/// the inner binding and the definition would compute `2` where Lean says
/// `1 + x`.
///
/// So a source binder that collides with a name already bound in this body is
/// renamed, and references within its own body are rewritten to the new name.
/// Only on an actual collision: the common case keeps the name the source
/// wrote, which is what a reader of the generated code wants to see.
///
/// Uniqueness is what makes flattening sound at all, and the printer depends
/// on it a second time: `uses()` there counts reads by name with no scope of
/// its own, so two live bindings sharing a name would corrupt the decision to
/// fold a temporary into its single use.
struct Lowering<'a> {
    params: &'a [(String, Type)],
    shapes: &'a Signatures<'a>,
    profile: &'a TargetProfile,
    next_temp: usize,
    /// Every name the source definition binds anywhere, collected up front. A
    /// generated temporary must avoid all of them, including binders it has
    /// not reached yet.
    reserved: BTreeSet<String>,
    /// Target names bound so far, parameters included. Membership here is
    /// exactly the collision test.
    bound: BTreeSet<String>,
    /// Source name -> target name, for the binders whose body the lowering is
    /// currently inside. Popped on the way out, so a sibling `let` of the same
    /// name does not resolve through it.
    scope: Vec<(String, String)>,
    /// Target name -> type, for every binding made. Never popped: target names
    /// are unique, so an entry can never be shadowed.
    types: Vec<(String, Type)>,
    /// The module's own type declarations, or empty when there is no module.
    /// Consulted for constructor arity and field existence -- questions about
    /// the IR, not about any target.
    decls: &'a [TypeDecl],
    /// Join-point declarations and their call counts, collected once for the
    /// whole body.
    jps: JpContext<'a>,
}

impl<'a> Lowering<'a> {
    fn fresh(&mut self) -> String {
        loop {
            let name = format!("t{}", self.next_temp);
            self.next_temp += 1;
            if !self.reserved.contains(&name) && !self.bound.contains(&name) {
                self.bound.insert(name.clone());
                return name;
            }
        }
    }

    /// The target name for a source binder: its own, or a fresh one if that is
    /// already taken.
    fn bind_source(&mut self, name: &str) -> String {
        if self.bound.contains(name) {
            return self.fresh();
        }
        self.bound.insert(String::from(name));
        String::from(name)
    }

    /// The target name a source `Var` refers to: the innermost binder of that
    /// name whose body we are inside, or the name itself (a parameter, or a
    /// name this slice does not bind).
    fn resolve(&self, name: &str) -> String {
        self.scope
            .iter()
            .rev()
            .find(|(source, _)| source == name)
            .map(|(_, target)| target.clone())
            .unwrap_or_else(|| String::from(name))
    }

    fn expr(&mut self, e: &Expr, stmts: &mut Vec<Stmt>) -> Result<TExpr, LowerError> {
        match e {
            Expr::Nat(n) => Ok(TExpr::Lit(Lit::Nat(*n))),
            Expr::Int(n) => Ok(TExpr::Lit(Lit::Int(*n))),
            Expr::Bool(b) => Ok(TExpr::Lit(Lit::Bool(*b))),
            Expr::Var(name) => Ok(TExpr::Var(self.resolve(name))),
            Expr::Param(index) => self
                .params
                .get(*index)
                .map(|(name, _)| TExpr::Var(name.clone()))
                .ok_or(LowerError::ParamOutOfBounds(*index)),

            Expr::Add(k, a, b) => self.arith(e, *k, BinOp::Add, a, b, stmts),
            Expr::Sub(k, a, b) => self.arith(e, *k, BinOp::Sub, a, b, stmts),
            Expr::Mul(k, a, b) => self.arith(e, *k, BinOp::Mul, a, b, stmts),
            Expr::Div(k, a, b) => {
                let op = self.division_op(*k, DivMod::Div);
                self.arith(e, *k, op, a, b, stmts)
            }
            Expr::Mod(k, a, b) => {
                let op = self.division_op(*k, DivMod::Mod);
                self.arith(e, *k, op, a, b, stmts)
            }
            // Shifts on `Int` are a deliberate non-goal, rejected here rather
            // than in a printer: the printers are total by construction, so a
            // construct no backend will render must be refused where the
            // semantics live.
            Expr::Shl(k, a, b) => {
                reject_int_shift(*k)?;
                self.arith(e, *k, BinOp::Shl, a, b, stmts)
            }
            Expr::Shr(k, a, b) => {
                reject_int_shift(*k)?;
                self.arith(e, *k, BinOp::Shr, a, b, stmts)
            }
            // Sized `pow` is rejected, not rendered: narrowing a `u64`
            // exponent to the `u32` that `wrapping_pow` takes would silently
            // compute a different number, and `pow` has no absorbing
            // out-of-range case the way a shift does.
            Expr::Pow(k, a, b) => {
                reject_sized_pow(*k)?;
                self.arith(e, *k, BinOp::Pow, a, b, stmts)
            }
            // Comparisons, connectives and conversions are TOTAL: none of
            // them can fail under any profile, so each yields a `TExpr`
            // directly and none is ever a `TryLet`.
            Expr::Eq(a, b) => self.compare_op(BinOp::Eq, a, b, stmts),
            Expr::Lt(a, b) => self.compare_op(BinOp::Lt, a, b, stmts),
            Expr::Le(a, b) => self.compare_op(BinOp::Le, a, b, stmts),
            Expr::Gt(a, b) => self.compare_op(BinOp::Gt, a, b, stmts),

            Expr::And(a, b) => {
                let (a, b) = self.connective(e, a, b, stmts)?;
                Ok(TExpr::And(Box::new(a), Box::new(b)))
            }
            Expr::Or(a, b) => {
                let (a, b) = self.connective(e, a, b, stmts)?;
                Ok(TExpr::Or(Box::new(a), Box::new(b)))
            }
            // `Not` is strict in its only operand, so whatever that operand
            // needs is evaluated anyway and may be hoisted freely.
            Expr::Not(a) => Ok(TExpr::Not(Box::new(self.expr(a, stmts)?))),

            // `Nat -> UIntN` is Lean's `Nat.toUIntN`, which TRUNCATES
            // (`BitVec` truncation), so it needs the same mask an arithmetic
            // result does on a host with no fixed-width integers. Rust's `as`
            // truncates on its own; an unbounded-integer host's conversion
            // does not.
            Expr::Convert(from, to, a) => {
                check_conversion(*from, *to)?;
                let value = TExpr::Convert(*from, *to, Box::new(self.expr(a, stmts)?));
                Ok(self.mask_sized(*to, value))
            }

            Expr::Neg(k, a) => {
                reject_non_int_neg(*k)?;
                let value = self.expr(a, stmts)?;
                if self.profile.op_is_fallible(e) {
                    Ok(self.bind_fallible(Type::Int, FallibleOp::Neg(*k, value), stmts))
                } else {
                    // Unreachable today -- every profile makes `Int` negation
                    // fallible -- and `TExpr` has no unary minus to fall back
                    // on, so a profile that made it total would need a node
                    // this slice does not define.
                    Err(LowerError::OpaqueExpr(String::from("total Neg")))
                }
            }

            // The value is lowered BEFORE the binder is in scope, so a
            // `let x := x + 1` still reads the outer `x` on the right.
            Expr::Let(name, value, body) => {
                let bound = self.bind_let(name, value, stmts)?;
                let out = self.expr(body, stmts);
                if bound {
                    self.scope.pop();
                }
                out
            }

            // A join point declaration in VALUE position. Its body is the
            // declaration's value when nothing jumps to it; when something
            // does, the body belongs at the jump site and the declaration
            // itself has no value to give. `bind_let` elides the `let` that
            // LCNF wraps it in, so reaching the second case means the `jp`
            // sat somewhere a value was actually wanted.
            Expr::Jp { name, body, .. } => {
                if self.jps.jmp_count(name) == 0 {
                    self.expr(body, stmts)
                } else {
                    // Something jumps to it, so its body belongs at the jump
                    // site and the declaration has no value to give. Either
                    // it is inlineable and `bind_let` could not elide the
                    // `let` LCNF wraps it in -- so there is no jump site to
                    // inline it at -- or it is cyclic or multi-caller. A join
                    // point this lowering will not place, either way, which is
                    // what the name says.
                    Err(LowerError::UnsupportedJoinPoint(name.clone()))
                }
            }

            Expr::Jmp(name, args) => {
                let (body, pushed) = self.inline_jmp(name, args, stmts)?;
                let out = self.expr(body, stmts);
                self.scope.truncate(self.scope.len() - pushed);
                out
            }

            Expr::Call(name, args) => {
                let mut lowered = Vec::with_capacity(args.len());
                for arg in args {
                    lowered.push(self.expr(arg, stmts)?);
                }
                match self.shapes.get(name.as_str()) {
                    Some(Shape::Fallible) => Ok(self.bind_fallible(
                        unknown_type(),
                        FallibleOp::Call(name.clone(), lowered),
                        stmts,
                    )),
                    // Not scaffolding: a list has no by-value form in the
                    // allocation-free tier, so its result cannot be an
                    // intermediate. `prod-codegen` refuses this in the same
                    // words, and the refusal outlives Task 7.
                    Some(Shape::Buffer) | Some(Shape::StaticList) => {
                        Err(LowerError::UnsupportedList(format!(
                            "`{}` returns a list; its result cannot be used as an intermediate value",
                            name
                        )))
                    }
                    Some(Shape::Value) | None => Ok(TExpr::Call(name.clone(), lowered)),
                }
            }

            // The list constructors have no value form either: they build
            // into the output sequence, which is `Position::List`, not here.
            // Falling through to the general constructor arm below would put
            // a `TExpr::Ctor` nobody can print into the body.
            Expr::Ctor(name, args)
                if (name == "List.nil" && args.is_empty())
                    || (name == "List.cons" && args.len() == 2) =>
            {
                Err(LowerError::UnsupportedList(format!(
                    "`{}` outside a list return position",
                    name
                )))
            }

            // Constructing and projecting are both TOTAL: neither can fail in
            // any target, so both stay in expression position rather than
            // becoming a `TryLet`.
            //
            // The constructor keeps its full LEAN name: that is the key a
            // printer resolves against `CtorDef::lean_name`, and it is the
            // only key an `Arm` has, so both sides of a type share one
            // resolver rather than two that can disagree.
            Expr::Ctor(name, args) => {
                let mut lowered = Vec::with_capacity(args.len());
                for arg in args {
                    lowered.push(self.expr(arg, stmts)?);
                }
                ctor_expr(self.decls, name, lowered)
            }

            // Field first, operand second -- the same order, and for the
            // same published-kind reason, as the invariant path above.
            Expr::Proj(ty, field, value) => {
                check_projected_field(self.decls, ty, field)?;
                let value = self.expr(value, stmts)?;
                Ok(TExpr::Proj(ty.clone(), field.clone(), Box::new(value)))
            }

            // The exporter reached a construct it could not describe.
            // `prod-codegen` reported `Error::OpaqueExpr` here and so does
            // this.
            Expr::Opaque(what) => Err(LowerError::OpaqueExpr(what.clone())),

            // A callee that is neither `@[prod]`-tagged nor whitelisted:
            // there is nothing to call. `prod-codegen`'s `UnresolvedCall`,
            // kept under its own name rather than folded into a generic
            // refusal.
            Expr::Extern(name, _) => Err(LowerError::UnresolvedCall(name.clone())),

            // `If`, `Match` and `Unreachable` are STATEMENTS in this IR --
            // `flow` lowers all three -- so in operand position they have no
            // total-expression form to become. LCNF's A-normal form puts them
            // in tail position, where `flow` sees them first; reaching here
            // means one was nested inside an operand, which is a shape this
            // slice does not lower.
            other => Err(LowerError::OpaqueExpr(String::from(node_name(other)))),
        }
    }

    /// Lower `e` in TAIL position: the statements it needs, ending in a
    /// terminator ([`Stmt::Return`], [`Stmt::If`], [`Stmt::Switch`] or
    /// [`Stmt::Fail`]).
    ///
    /// [`Position`] says what the tail *is*: a value to return, or elements
    /// to append to the definition's output sequence. Control flow is
    /// identical either way -- an `if` in a list-shaped definition is still an
    /// `if`, and its branches are still separate statement lists -- so there
    /// is one implementation of it rather than one per position. The two
    /// diverged in the renderer this replaced, where `Mode::Value` and
    /// `Mode::Builder` each re-derived the same match lowering.
    ///
    /// # Why branches get their own accumulator
    ///
    /// **A `TryLet` must never cross a control-flow boundary.** Every branch
    /// is lowered into a `Vec<Stmt>` of its own, so nothing a branch needs can
    /// be lifted into the enclosing list. Hoisting a branch's `TryLet` to the
    /// top would evaluate it even when the branch does not run -- turning a
    /// short-circuit into eager evaluation, and reporting an overflow where
    /// Lean, whose `Nat` is unbounded and whose `if` is lazy in its arms, has
    /// no failure at all. That is not a formatting difference; it is a
    /// different function.
    ///
    /// The scrutinee and the condition are lowered into the ENCLOSING list on
    /// purpose: they are evaluated unconditionally, whichever way the branch
    /// goes.
    fn flow(
        &mut self,
        e: &'a Expr,
        pos: Position<'_>,
        env: &mut Vec<ListBinding<'a>>,
        stmts: &mut Vec<Stmt>,
    ) -> Result<(), LowerError> {
        match e {
            Expr::If(cond, then_, else_) => {
                let cond = self.expr(cond, stmts)?;
                let mut then_stmts: Vec<Stmt> = Vec::new();
                self.flow(then_, pos, env, &mut then_stmts)?;
                let mut else_stmts: Vec<Stmt> = Vec::new();
                self.flow(else_, pos, env, &mut else_stmts)?;
                stmts.push(Stmt::If {
                    cond,
                    then: then_stmts,
                    else_: else_stmts,
                });
                Ok(())
            }

            Expr::Match {
                scrut,
                alts,
                default,
            } => {
                let scrut = self.expr(scrut, stmts)?;
                let mut arms = Vec::with_capacity(alts.len());
                for alt in alts {
                    // The same arity agreement as on the construction side,
                    // and rejected in the same words. Without it the printer
                    // falls through to its positional pattern and emits
                    // `M.Shape.circle(r, extra)` -- a dotted Lean name used as
                    // a Rust path, with one binder too many. Naming the reason
                    // beats emitting code that does not compile, and this is
                    // the layer that can tell the difference, because the
                    // printers are total by construction.
                    if let Some((_, cdecl)) = ctor_decl(self.decls, &alt.ctor) {
                        if alt.binders.len() != cdecl.fields.len() {
                            return Err(LowerError::UnsupportedFieldType(format!(
                                "`{}` takes {} field(s) but got {} binder(s)",
                                alt.ctor,
                                cdecl.fields.len(),
                                alt.binders.len()
                            )));
                        }
                    }
                    // An alternative's binders are source binders like any
                    // other: they go through `bind_source`, so one that
                    // shadows a parameter is renamed, and through `scope`, so
                    // reads inside the arm resolve to the renamed binder.
                    // Without both, the printer's `uses()` -- which counts
                    // reads by name and has no scope of its own -- would pool
                    // the arm's reads with the parameter's.
                    let mut binders = Vec::with_capacity(alt.binders.len());
                    for binder in &alt.binders {
                        let target = self.bind_source(binder);
                        self.scope.push((binder.clone(), target.clone()));
                        binders.push(target);
                    }
                    let mut body: Vec<Stmt> = Vec::new();
                    let out = self.flow(&alt.body, pos, env, &mut body);
                    self.scope.truncate(self.scope.len() - alt.binders.len());
                    out?;
                    arms.push(Arm {
                        ctor: alt.ctor.clone(),
                        binders,
                        body,
                    });
                }
                let default = match default {
                    Some(d) => {
                        let mut body: Vec<Stmt> = Vec::new();
                        self.flow(d, pos, env, &mut body)?;
                        Some(body)
                    }
                    None => None,
                };
                stmts.push(Stmt::Switch {
                    scrut,
                    arms,
                    default,
                });
                Ok(())
            }

            // A branch LCNF proved dead. It is a terminator, not a value, so
            // it has no lowering in operand position.
            Expr::Unreachable => {
                stmts.push(Stmt::Fail(ErrorCode::Unreachable));
                Ok(())
            }

            Expr::Let(name, value, body) => {
                // A `let` whose value is a LIST has no runtime representation
                // to bind: the elements go into the output sequence at the
                // point the list is consumed, not where it is named. LCNF
                // writes cons chains in A-normal form, so this is the usual
                // spelling rather than an exotic one, and recording the
                // binding here is what lets the tail of a cons be a `Var`.
                if let Position::List { .. } = pos {
                    if self.is_list_valued(value, env) {
                        // The scope depth goes in with the binding: `append`
                        // re-lowers `value` from somewhere else in the
                        // traversal and has to see the scope this `let` was
                        // written in, not the one it is consumed in.
                        env.push(ListBinding {
                            name: name.clone(),
                            value,
                            scope: self.scope.len(),
                        });
                        let out = self.flow(body, pos, env, stmts);
                        env.pop();
                        return out;
                    }
                }
                let bound = self.bind_let(name, value, stmts)?;
                let out = self.flow(body, pos, env, stmts);
                if bound {
                    self.scope.pop();
                }
                out
            }

            Expr::Jp { name, body, .. } if self.jps.jmp_count(name) == 0 => {
                self.flow(body, pos, env, stmts)
            }

            Expr::Jmp(name, args) => {
                let (body, pushed) = self.inline_jmp(name, args, stmts)?;
                let out = self.flow(body, pos, env, stmts);
                self.scope.truncate(self.scope.len() - pushed);
                out
            }

            other => match pos {
                // Everything else is a value: lower it and return it.
                Position::Value => {
                    let value = self.expr(other, stmts)?;
                    stmts.push(Stmt::Return(value));
                    Ok(())
                }
                Position::List { seq, bounded } => self.append(other, seq, bounded, env, stmts),
            },
        }
    }

    /// Lower `e` as the remaining elements of the output sequence `seq`.
    ///
    /// Reached only from [`Lowering::flow`], so control flow is already
    /// handled; what is left is the three ways a list ends up being built.
    ///
    /// `bounded` is the caller-supplied-buffer case, and it is the whole
    /// reason this is a lowering rather than a printer: running out of that
    /// buffer is a FAILURE, and by this IR's central invariant a failure
    /// belongs in statement position. It used to live inside the Rust
    /// renderer, where three printers would be three chances to forget it.
    fn append(
        &mut self,
        e: &'a Expr,
        seq: &str,
        bounded: bool,
        env: &mut Vec<ListBinding<'a>>,
        stmts: &mut Vec<Stmt>,
    ) -> Result<(), LowerError> {
        match e {
            // The empty list appends nothing, so the definition is done and
            // reports how much of the sequence it used.
            Expr::Ctor(name, args) if name == "List.nil" && args.is_empty() => {
                stmts.push(Stmt::Return(TExpr::Seq(SeqQuery::Len, String::from(seq))));
                Ok(())
            }

            Expr::Ctor(name, args) if name == "List.cons" && args.len() == 2 => {
                // The guard is emitted BEFORE the head is lowered, so a head
                // whose arithmetic can fail reports `OutputTooSmall` first --
                // the order `prod-codegen` renders, where the head is written
                // inside the arm that found room for it.
                if bounded {
                    stmts.push(Stmt::If {
                        cond: TExpr::BinOp(
                            NumKind::Nat,
                            BinOp::Lt,
                            Box::new(TExpr::Seq(SeqQuery::Len, String::from(seq))),
                            Box::new(TExpr::Seq(SeqQuery::Cap, String::from(seq))),
                        ),
                        then: Vec::new(),
                        else_: alloc::vec![Stmt::Fail(ErrorCode::OutputTooSmall)],
                    });
                }
                let value = self.expr(&args[0], stmts)?;
                stmts.push(Stmt::Push {
                    seq: String::from(seq),
                    value,
                });
                // The tail goes back through `flow`, not straight to
                // `append`: it may be a `let`, an `if` or a match, and those
                // have one lowering, not one per position.
                self.flow(&args[1], Position::List { seq, bounded }, env, stmts)
            }

            // A list named by a `let` this definition made: continue with what
            // it was bound to, in the environment AND the scope that were in
            // effect where the binding was written -- so `let x := x` cannot
            // resolve to itself, and a binder introduced between the `let` and
            // its consumption cannot capture a `Var` inside it.
            //
            // BOTH are rewound. `env` is rewound by position; `self.scope` is
            // rewound to the depth recorded in the binding, the same way
            // `flow`'s `Jmp` arm truncates what `inline_jmp` pushed. Rewinding
            // only `env` was a real defect: it left this arm reading `scope`
            // at a point in the traversal other than where the bound
            // expression was written, which is exactly the capture the
            // uniquification work exists to prevent.
            Expr::Var(name) => match env.iter().rposition(|b| b.name == *name) {
                Some(index) => {
                    let bound = env[index].value;
                    let depth = env[index].scope;
                    let inner = env.split_off(index);
                    // `flow` is scope-balanced -- every arm that pushes pops
                    // again -- so what is set aside here is exactly what was
                    // bound after the `let`, and it all comes back.
                    let outer = self.scope.split_off(depth);
                    let out = self.flow(bound, Position::List { seq, bounded }, env, stmts);
                    self.scope.extend(outer);
                    env.extend(inner);
                    out
                }
                None => Err(LowerError::UnsupportedList(format!(
                    "`{}` is not a list built in this definition",
                    name
                ))),
            },

            // A callee that builds a list appends to the SAME sequence,
            // starting where this definition left off, and reports how many
            // elements it added.
            //
            // The call stays an ordinary fallible call -- the callee is the
            // one that can run out of room and say so -- and the cursor moves
            // in a separate, infallible `Advance`. That is what keeps
            // `TryLet` the only failure point in the language.
            Expr::Call(name, args) if self.shapes.get(name.as_str()) == Some(&Shape::Buffer) => {
                let mut lowered = Vec::with_capacity(args.len() + 1);
                for arg in args {
                    lowered.push(self.expr(arg, stmts)?);
                }
                lowered.push(TExpr::Seq(SeqQuery::Rest, String::from(seq)));
                let count = self.bind_fallible(
                    unknown_type(),
                    FallibleOp::Call(name.clone(), lowered),
                    stmts,
                );
                stmts.push(Stmt::Advance {
                    seq: String::from(seq),
                    count,
                });
                stmts.push(Stmt::Return(TExpr::Seq(SeqQuery::Len, String::from(seq))));
                Ok(())
            }

            // Both messages are `prod-codegen`'s, verbatim: the rejection
            // wording is pinned by the published subset contract, so it moves
            // across the split without being improved.
            Expr::Call(name, _) => Err(LowerError::UnsupportedList(format!(
                "`{}` does not build its list into a caller buffer",
                name
            ))),

            _ => Err(LowerError::UnsupportedList(String::from(
                "expression does not build a list",
            ))),
        }
    }

    /// Is this the value of a list-typed binding -- one with no runtime
    /// representation of its own, to be resolved where the list is consumed?
    fn is_list_valued(&self, e: &Expr, env: &[ListBinding<'a>]) -> bool {
        match e {
            Expr::Ctor(name, _) => name == "List.nil" || name == "List.cons",
            Expr::Call(name, _) => matches!(
                self.shapes.get(name.as_str()),
                Some(Shape::Buffer) | Some(Shape::StaticList)
            ),
            Expr::Var(name) => env.iter().any(|b| b.name == *name),
            _ => false,
        }
    }

    /// A comparison in a definition body, through the same [`compare`] the
    /// invariant path uses.
    fn compare_op(
        &mut self,
        op: BinOp,
        a: &Expr,
        b: &Expr,
        stmts: &mut Vec<Stmt>,
    ) -> Result<TExpr, LowerError> {
        let a = self.expr(a, stmts)?;
        let b = self.expr(b, stmts)?;
        Ok(compare(op, a, b, &|name: &str| {
            type_kind(&self.var_type(name))
        }))
    }

    /// Both operands of `And`/`Or`, refusing the one shape this IR cannot say.
    ///
    /// **They are LAZY in the right operand**, and `TExpr` has no statement
    /// list to hang a lazy operand's work on. Lowering the right operand into
    /// the enclosing statement list would evaluate it unconditionally, so a
    /// `Nat` addition inside it would report an overflow on inputs where Lean
    /// -- whose `Nat` is unbounded and whose `&&` is short-circuiting -- has
    /// no failure at all. That is a different function, not a different
    /// formatting, so it is refused rather than emitted.
    ///
    /// No definition in any corpus reaches this: the boolean connectives
    /// appear in structure invariants, where an operation that can fail is
    /// already refused outright, and never in a definition body.
    fn connective(
        &mut self,
        node: &Expr,
        a: &Expr,
        b: &Expr,
        stmts: &mut Vec<Stmt>,
    ) -> Result<(TExpr, TExpr), LowerError> {
        let a = self.expr(a, stmts)?;
        let mut lazy: Vec<Stmt> = Vec::new();
        let b = self.expr(b, &mut lazy)?;
        if !lazy.is_empty() {
            return Err(LowerError::OpaqueExpr(format!(
                "{} whose right operand needs statements, which would evaluate it eagerly",
                node_name(node)
            )));
        }
        Ok((a, b))
    }

    /// Emit the binding for a source `let` and put it in scope. Returns
    /// whether a scope entry was pushed, so the caller knows to pop it.
    ///
    /// The value is lowered BEFORE the binder is in scope, so a
    /// `let x := x + 1` still reads the outer `x` on the right.
    fn bind_let(
        &mut self,
        name: &str,
        value: &Expr,
        stmts: &mut Vec<Stmt>,
    ) -> Result<bool, LowerError> {
        // LCNF writes a join point as `let g := jp g (..) ..; <continuation>`.
        // When the join point is inlined at its jump site the declaration has
        // nothing left to bind, so the `let` disappears entirely rather than
        // binding a unit nobody reads.
        if let Expr::Jp { name: jp, .. } = value {
            if self.jps.is_inlineable(jp) {
                return Ok(false);
            }
        }
        let value = self.expr(value, stmts)?;
        let ty = self.type_of(&value);
        let target = self.bind_source(name);
        stmts.push(Stmt::Let {
            name: target.clone(),
            ty: ty.clone(),
            value,
        });
        self.types.push((target.clone(), ty));
        self.scope.push((String::from(name), target));
        Ok(true)
    }

    /// Bind a join point's parameters at its jump site and hand back its body
    /// for the caller to lower in whatever position the `jmp` itself was in,
    /// plus the number of scope entries to pop afterwards.
    ///
    /// Only the single-caller, non-cyclic form is inlined; everything else is
    /// [`LowerError::UnsupportedJoinPoint`], which is exactly the set
    /// `prod-codegen` rejects today. Widening that is not this task.
    ///
    /// The arguments are all lowered before any parameter is bound: they are
    /// evaluated in the CALLER's scope, so a later argument must not read a
    /// parameter this jump is in the middle of binding.
    fn inline_jmp(
        &mut self,
        name: &str,
        args: &[Expr],
        stmts: &mut Vec<Stmt>,
    ) -> Result<(&'a Expr, usize), LowerError> {
        let Some((params, body)) = self.jps.decls.get(name).copied() else {
            return Err(LowerError::UnsupportedJoinPoint(String::from(name)));
        };
        if !self.jps.is_inlineable(name) {
            return Err(LowerError::UnsupportedJoinPoint(String::from(name)));
        }
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(self.expr(arg, stmts)?);
        }
        let mut pushed = 0;
        for (param, value) in params.iter().zip(values) {
            let ty = self.type_of(&value);
            let target = self.bind_source(param);
            stmts.push(Stmt::Let {
                name: target.clone(),
                ty: ty.clone(),
                value,
            });
            self.types.push((target.clone(), ty));
            self.scope.push((param.clone(), target));
            pushed += 1;
        }
        Ok((body, pushed))
    }

    /// Lower a binary arithmetic node, hoisting it to a [`Stmt::TryLet`]
    /// exactly when the profile says it can fail.
    fn arith(
        &mut self,
        node: &Expr,
        kind: NumKind,
        op: BinOp,
        a: &Expr,
        b: &Expr,
        stmts: &mut Vec<Stmt>,
    ) -> Result<TExpr, LowerError> {
        let a = self.expr(a, stmts)?;
        let b = self.expr(b, stmts)?;
        let value = if self.profile.op_is_fallible(node) {
            self.bind_fallible(kind_type(kind), FallibleOp::Arith(kind, op, a, b), stmts)
        } else {
            TExpr::BinOp(kind, op, Box::new(a), Box::new(b))
        };
        Ok(self.mask_sized(kind, value))
    }

    /// Reduce a sized-kind result to its own width, on a host that has no
    /// fixed-width integers.
    ///
    /// Lean's `UInt8.add` is `BitVec` addition: it *wraps*, and that wrapping
    /// is the semantics, not an overflow. A host whose integers are unbounded
    /// -- [`TargetProfile::sized_mask_required`] -- computes the mathematical
    /// sum instead, so the lowering owes it an explicit `& 0xff`.
    ///
    /// # Why the lowering and not the printer
    ///
    /// Masking after a *sequence* of operations is a different function from
    /// masking each one: `(a + b) * c` masked once at the end agrees with Lean
    /// only when the intermediate sum did not exceed the width. A printer sees
    /// one node at a time and would have to re-derive where the boundaries
    /// are; here every operation carries its own mask by construction, so
    /// composition is right for free.
    ///
    /// Applied to every sized-kind arithmetic result rather than only to the
    /// operations that can widen (`add`, `mul`, `shl`). `div`, `mod` and `shr`
    /// cannot leave the range their operands were already in, so their masks
    /// are redundant -- but "mask every sized result" is a rule the next
    /// operator inherits, and "mask the widening ones" is a list someone has
    /// to remember to extend.
    fn mask_sized(&self, kind: NumKind, value: TExpr) -> TExpr {
        if !self.profile.sized_mask_required {
            return value;
        }
        match sized_mask(kind) {
            Some(mask) => TExpr::BinOp(
                kind,
                BinOp::BitAnd,
                Box::new(value),
                Box::new(TExpr::Lit(Lit::Nat(mask))),
            ),
            None => value,
        }
    }

    /// Which division operator computes *Lean's* answer on this host.
    ///
    /// Lean's `Int` division is Euclidean (`Int.ediv`/`Int.emod`, "for
    /// compatibility with SMT-LIB"): `(-12) / 7 = -2` and `(-12) % 7 = 2`,
    /// where a truncating host gives `-1` and `-5` and a flooring host agrees
    /// only while the divisor is positive. Whether that needs correcting is a
    /// property of the host, declared once in
    /// [`TargetProfile::host_division`] -- not something each printer decides.
    ///
    /// `Nat` and the sized kinds are unsigned, where truncating, flooring and
    /// Euclidean division all coincide, so no host needs a correction there.
    fn division_op(&self, kind: NumKind, which: DivMod) -> BinOp {
        let needs_correction =
            kind == NumKind::Int && self.profile.host_division != DivisionSemantics::Euclidean;
        match (which, needs_correction) {
            (DivMod::Div, false) => BinOp::Div,
            (DivMod::Div, true) => BinOp::DivE,
            (DivMod::Mod, false) => BinOp::Mod,
            (DivMod::Mod, true) => BinOp::ModE,
        }
    }

    fn bind_fallible(&mut self, ty: Type, op: FallibleOp, stmts: &mut Vec<Stmt>) -> TExpr {
        let name = self.fresh();
        stmts.push(Stmt::TryLet {
            name: name.clone(),
            ty: ty.clone(),
            op,
        });
        self.types.push((name.clone(), ty));
        TExpr::Var(name)
    }

    /// Best-effort type of a lowered expression, for the binder it is about to
    /// be bound to.
    fn type_of(&self, e: &TExpr) -> Type {
        match e {
            TExpr::Lit(Lit::Nat(_)) => Type::Nat,
            TExpr::Lit(Lit::Int(_)) => Type::Int,
            TExpr::Lit(Lit::Bool(_)) => Type::Bool,
            TExpr::BinOp(kind, op, ..) => match op {
                BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt => Type::Bool,
                _ => kind_type(*kind),
            },
            TExpr::Not(_) | TExpr::And(..) | TExpr::Or(..) => Type::Bool,
            // A conversion's type is the kind it converts TO -- that is what
            // it is for.
            TExpr::Convert(_, to, _) => kind_type(*to),
            // Every question about a sequence answers with a count.
            TExpr::Seq(..) => Type::Nat,
            TExpr::Var(name) => self.var_type(name),
            TExpr::Call(..) | TExpr::Ctor(..) | TExpr::Proj(..) => unknown_type(),
        }
    }

    /// The type a bound name was given: the definition-body path's answer to
    /// the question [`field_kind`] answers for an invariant.
    ///
    /// Parameters are searched after generated binders, and both in reverse,
    /// so the most recent binding of a name wins -- though the lowering makes
    /// every binder unique, so in practice there is only ever one.
    fn var_type(&self, name: &str) -> Type {
        self.types
            .iter()
            .rev()
            .chain(self.params.iter().rev())
            .find(|(bound, _)| bound == name)
            .map(|(_, ty)| ty.clone())
            .unwrap_or_else(unknown_type)
    }
}

/// Join-point analysis for one definition body.
///
/// Ported unchanged from `prod-codegen`'s renderer, deliberately: the policy
/// it encodes -- inline the single-caller, non-cyclic form, reject the rest --
/// is the behaviour the Task 7 cutover has to reproduce, so it moves without
/// being widened.
///
/// *Behaviour*, not text. The cutover kept the function and not the spelling:
/// a list body renders as a flat `__len` cursor where the renderer this
/// replaced nested `split_first_mut`, which computes the same function and
/// does not spell it the same way.
struct JpContext<'a> {
    /// name -> (params, body) of each `jp` declaration in the body
    decls: BTreeMap<&'a str, (&'a [String], &'a Expr)>,
    /// name -> total number of `jmp` sites in the body
    jmp_counts: BTreeMap<&'a str, usize>,
}

impl<'a> JpContext<'a> {
    fn collect(body: &'a Expr) -> Self {
        let mut ctx = JpContext {
            decls: BTreeMap::new(),
            jmp_counts: BTreeMap::new(),
        };
        ctx.walk(body);
        ctx
    }

    fn walk(&mut self, expr: &'a Expr) {
        match expr {
            Expr::Jp { name, params, body } => {
                self.decls.insert(name.as_str(), (params, body));
            }
            Expr::Jmp(name, _) => {
                *self.jmp_counts.entry(name.as_str()).or_insert(0) += 1;
            }
            _ => {}
        }
        for child in expr.children() {
            self.walk(child);
        }
    }

    fn jmp_count(&self, name: &str) -> usize {
        self.jmp_counts.get(name).copied().unwrap_or(0)
    }

    /// A join point is cyclic if a jump to it occurs inside its own body.
    fn is_cyclic(&self, name: &str) -> bool {
        match self.decls.get(name) {
            Some((_, body)) => count_jmps(body, name) > 0,
            None => false,
        }
    }

    /// Inlineable: exactly one caller, and not self-referential.
    fn is_inlineable(&self, name: &str) -> bool {
        self.jmp_count(name) == 1 && !self.is_cyclic(name)
    }
}

/// Number of `jmp <name>` sites within `expr`.
fn count_jmps(expr: &Expr, name: &str) -> usize {
    let self_count = match expr {
        Expr::Jmp(n, _) if n == name => 1,
        _ => 0,
    };
    self_count + expr.children().map(|c| count_jmps(c, name)).sum::<usize>()
}

/// The mask that reduces a value to `kind`'s width: `2^width - 1`.
///
/// `None` for the two unbounded kinds -- Lean's `Nat` and `Int` have no width
/// to reduce to, and a backend that bounds them says so through
/// [`TargetProfile::nat_repr`] instead, which is a fallibility question rather
/// than a masking one.
fn sized_mask(kind: NumKind) -> Option<u64> {
    match kind {
        NumKind::U8 => Some(u8::MAX as u64),
        NumKind::U16 => Some(u16::MAX as u64),
        NumKind::U32 => Some(u32::MAX as u64),
        NumKind::U64 => Some(u64::MAX),
        NumKind::Nat | NumKind::Int => None,
    }
}

fn kind_type(kind: NumKind) -> Type {
    match kind {
        NumKind::Nat => Type::Nat,
        NumKind::Int => Type::Int,
        other => Type::UInt(other),
    }
}

/// The type a binder gets when this slice cannot determine one.
///
/// [`Signatures`] records each definition's [`Shape`], not its return type, so
/// a call's result is untyped here, as are constructors and projections.
/// Rust's `let` infers, so `prod-emit-rust` never reads the field; a C backend
/// will, and widening the table consulted here is what that backend will need.
/// Spelled `Opaque` deliberately rather than guessed: a printer that does read
/// it then fails loudly instead of declaring the wrong type.
fn unknown_type() -> Type {
    Type::Opaque(String::from("?"))
}

fn reject_int_shift(kind: NumKind) -> Result<(), LowerError> {
    if kind == NumKind::Int {
        return Err(LowerError::UnsupportedKind(String::from(
            "shifts are not supported for Int",
        )));
    }
    Ok(())
}

/// Sized `pow` is rejected, not rendered: narrowing a `u64` exponent to the
/// `u32` that `wrapping_pow` takes would silently compute a different number,
/// and `pow` has no absorbing out-of-range case the way a shift does.
fn reject_sized_pow(kind: NumKind) -> Result<(), LowerError> {
    if !matches!(kind, NumKind::Nat | NumKind::Int) {
        return Err(LowerError::UnsupportedKind(format!(
            "pow is not supported for sized kind {:?} (unsound u32 exponent narrowing)",
            kind
        )));
    }
    Ok(())
}

fn reject_non_int_neg(kind: NumKind) -> Result<(), LowerError> {
    if kind != NumKind::Int {
        return Err(LowerError::UnsupportedKind(format!(
            "unary negation is only supported for Int, not {:?}",
            kind
        )));
    }
    Ok(())
}

/// Every name the definition binds: its parameters, its `let`s, its join
/// points and their parameters, and its match binders.
fn bound_names(def: &Definition) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = def.params.iter().map(|(n, _)| n.clone()).collect();
    collect_bound(&def.body, &mut out);
    out
}

fn collect_bound(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Let(name, ..) => {
            out.insert(name.clone());
        }
        Expr::Jp { name, params, .. } => {
            out.insert(name.clone());
            out.extend(params.iter().cloned());
        }
        Expr::Match { alts, .. } => {
            for alt in alts {
                out.extend(alt.binders.iter().cloned());
            }
        }
        _ => {}
    }
    for child in e.children() {
        collect_bound(child, out);
    }
}

/// The node name a rejection reports.
///
/// Exhaustive on purpose: a new `Expr` variant is a compile error here, which
/// is the prompt to give it a lowering rather than let it fall into a
/// wildcard. That is the property `LowerError::NotYetLowered` used to buy at
/// runtime, kept at compile time now that the variant is gone.
fn node_name(e: &Expr) -> &'static str {
    match e {
        Expr::Nat(_) => "Nat",
        Expr::Int(_) => "Int",
        Expr::Bool(_) => "Bool",
        Expr::Var(_) => "Var",
        Expr::Param(_) => "Param",
        Expr::Add(..) => "Add",
        Expr::Sub(..) => "Sub",
        Expr::Mul(..) => "Mul",
        Expr::Div(..) => "Div",
        Expr::Mod(..) => "Mod",
        Expr::Shl(..) => "Shl",
        Expr::Shr(..) => "Shr",
        Expr::Pow(..) => "Pow",
        Expr::Neg(..) => "Neg",
        Expr::Convert(..) => "Convert",
        Expr::Eq(..) => "Eq",
        Expr::Lt(..) => "Lt",
        Expr::Le(..) => "Le",
        Expr::Gt(..) => "Gt",
        Expr::If(..) => "If",
        Expr::Let(..) => "Let",
        Expr::Call(..) => "Call",
        Expr::Match { .. } => "Match",
        Expr::Ctor(..) => "Ctor",
        Expr::Proj(..) => "Proj",
        Expr::Jp { .. } => "Jp",
        Expr::Jmp(..) => "Jmp",
        Expr::Unreachable => "Unreachable",
        Expr::Opaque(_) => "Opaque",
        Expr::Extern(..) => "Extern",
        Expr::And(..) => "And",
        Expr::Or(..) => "Or",
        Expr::Not(..) => "Not",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::{DivisionSemantics, TargetProfile};
    use crate::shape::signatures;
    use crate::target::*;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use prod_ir::{Alt, Definition, Expr, NumKind, Type};

    fn def_add() -> Definition {
        Definition {
            name: String::from("f"),
            params: vec![
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            ),
        }
    }

    #[test]
    fn a_fallible_op_becomes_a_trylet_and_a_return() {
        let defs = vec![def_add()];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        assert_eq!(
            body.stmts.len(),
            2,
            "expected TryLet + Return, got {:?}",
            body.stmts
        );
        assert!(matches!(
            &body.stmts[0],
            Stmt::TryLet {
                op: FallibleOp::Arith(NumKind::Nat, BinOp::Add, ..),
                ..
            }
        ));
        match (&body.stmts[0], &body.stmts[1]) {
            (Stmt::TryLet { name, .. }, Stmt::Return(TExpr::Var(v))) => {
                assert_eq!(
                    v, name,
                    "the Return must name the temporary the TryLet bound"
                );
            }
            other => panic!(
                "expected TryLet then Return of its temporary, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn the_same_op_is_a_plain_binop_under_an_exact_nat_profile() {
        // Not a formatting difference: under Exact there is no failure to
        // hoist, so the statement list has a different SHAPE. This is the
        // fallibility decision being made once, in the lowering.
        let defs = vec![def_add()];
        let shapes = signatures(&defs, &TargetProfile::PYTHON);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::PYTHON).expect("lowers");

        assert_eq!(
            body.stmts.len(),
            1,
            "expected a bare Return, got {:?}",
            body.stmts
        );
        assert!(matches!(
            &body.stmts[0],
            Stmt::Return(TExpr::BinOp(NumKind::Nat, BinOp::Add, ..))
        ));
    }
    fn def_int_div(op: fn(NumKind, Box<Expr>, Box<Expr>) -> Expr) -> Definition {
        Definition {
            name: String::from("f"),
            params: vec![
                (String::from("a"), Type::Int),
                (String::from("b"), Type::Int),
            ],
            ret: Type::Int,
            body: op(
                NumKind::Int,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            ),
        }
    }

    /// The operator a lowered expression computes with, seen THROUGH the
    /// width mask a `sized_mask_required` profile wraps a sized result in.
    /// The mask is not the operation; it is what the host needs around it.
    fn arith_op(e: &TExpr) -> Option<BinOp> {
        match e {
            TExpr::BinOp(_, BinOp::BitAnd, inner, _) => arith_op(inner),
            TExpr::BinOp(_, op, ..) => Some(*op),
            _ => None,
        }
    }

    fn div_op(def: &Definition, profile: &TargetProfile) -> BinOp {
        let defs = vec![def.clone()];
        let shapes = signatures(&defs, profile);
        let body = lower_def(&defs[0], &shapes, profile).expect("lowers");
        for stmt in &body.stmts {
            match stmt {
                Stmt::TryLet {
                    op: FallibleOp::Arith(_, op, ..),
                    ..
                } => return *op,
                Stmt::Return(e) => {
                    if let Some(op) = arith_op(e) {
                        return op;
                    }
                }
                _ => {}
            }
        }
        panic!("no arithmetic operator in {:?}", body.stmts)
    }

    /// The Euclidean correction is the profile's decision, not the printer's.
    ///
    /// Lean's `Int` division is `Int.ediv`/`Int.emod`. A host that already
    /// divides that way needs no correction; one that truncates or floors
    /// does. Nothing downstream re-derives this -- the operator in the Target
    /// IR already says which.
    #[test]
    fn the_euclidean_correction_is_chosen_by_host_division() {
        let euclidean_host = TargetProfile {
            host_division: DivisionSemantics::Euclidean,
            ..TargetProfile::RUST
        };

        // Rust truncates: `(-12) / 7` is `-1` there and `-2` in Lean.
        assert_eq!(
            div_op(&def_int_div(Expr::Div), &TargetProfile::RUST),
            BinOp::DivE
        );
        assert_eq!(
            div_op(&def_int_div(Expr::Mod), &TargetProfile::RUST),
            BinOp::ModE
        );
        // Python floors, which agrees with Euclidean only while the divisor
        // is positive -- so it needs the correction too.
        assert_eq!(
            div_op(&def_int_div(Expr::Div), &TargetProfile::PYTHON),
            BinOp::DivE
        );
        // A host whose own division is Euclidean gets the plain operator.
        assert_eq!(div_op(&def_int_div(Expr::Div), &euclidean_host), BinOp::Div);
        assert_eq!(div_op(&def_int_div(Expr::Mod), &euclidean_host), BinOp::Mod);
    }

    /// Unsigned kinds need no correction under any host: truncating, flooring
    /// and Euclidean division all coincide on non-negative operands.
    #[test]
    fn unsigned_division_never_takes_the_euclidean_correction() {
        for kind in [NumKind::Nat, NumKind::U8, NumKind::U64] {
            let ty = if kind == NumKind::Nat {
                Type::Nat
            } else {
                Type::UInt(kind)
            };
            let def = Definition {
                name: String::from("f"),
                params: vec![
                    (String::from("a"), ty.clone()),
                    (String::from("b"), ty.clone()),
                ],
                ret: ty,
                body: Expr::Div(
                    kind,
                    Box::new(Expr::Var(String::from("a"))),
                    Box::new(Expr::Var(String::from("b"))),
                ),
            };
            assert_eq!(div_op(&def, &TargetProfile::RUST), BinOp::Div);
            assert_eq!(div_op(&def, &TargetProfile::PYTHON), BinOp::Div);
        }
    }

    /// A generated temporary must never collide with a name the definition
    /// binds: the printer may fold a temporary into its single use, and a
    /// `let t0` in between would shadow it.
    #[test]
    fn a_fresh_temporary_skips_a_name_the_source_already_binds() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("a"), Type::Nat)],
            ret: Type::Nat,
            // let t0 := a; t0 + t0
            body: Expr::Let(
                String::from("t0"),
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Add(
                    NumKind::Nat,
                    Box::new(Expr::Var(String::from("t0"))),
                    Box::new(Expr::Var(String::from("t0"))),
                )),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        let bound: Vec<&String> = body
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::TryLet { name, .. } => Some(name),
                _ => None,
            })
            .collect();
        assert_eq!(bound, vec![&String::from("t1")], "got {:?}", body.stmts);
    }
    /// The scoping the flattened statement list has to preserve by hand.
    ///
    /// `f(x) = (let x := 1; x) + x`. Lean's second operand is the PARAMETER --
    /// the inner binding's scope ends at the first operand. Hoisting
    /// `let x = 1;` into the enclosing list without renaming would put it in
    /// scope for the second operand too, and the definition would compute
    /// `1 + 1` where Lean says `1 + x`. The old renderer got this from the
    /// brace in `{ let x = 1; x } + x`; a flat list has no brace, so the
    /// lowering renames instead.
    #[test]
    fn a_let_shadowing_a_parameter_does_not_capture_later_uses() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Let(
                    String::from("x"),
                    Box::new(Expr::Nat(1)),
                    Box::new(Expr::Var(String::from("x"))),
                )),
                Box::new(Expr::Var(String::from("x"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        let inner = match &body.stmts[0] {
            Stmt::Let { name, .. } => name.clone(),
            other => panic!("expected the hoisted Let first, got {:?}", other),
        };
        assert_ne!(inner, "x", "the inner binder must be renamed off the param");

        match &body.stmts[1] {
            Stmt::TryLet {
                op: FallibleOp::Arith(_, BinOp::Add, a, b),
                ..
            } => {
                assert_eq!(a, &TExpr::Var(inner), "first operand is the inner binding");
                assert_eq!(
                    b,
                    &TExpr::Var(String::from("x")),
                    "second operand must still be the PARAMETER, got {:?}",
                    b
                );
            }
            other => panic!("expected the add, got {:?}", other),
        }
    }

    /// Two sibling `let`s of the same name are two different bindings. The
    /// first one's value has already been read into an operand by the time the
    /// second is emitted, so the second must not take its name.
    #[test]
    fn sibling_lets_of_the_same_name_get_different_binders() {
        let shadow = |n: u64| {
            Expr::Let(
                String::from("y"),
                Box::new(Expr::Nat(n)),
                Box::new(Expr::Var(String::from("y"))),
            )
        };
        let def = Definition {
            name: String::from("f"),
            params: vec![],
            ret: Type::Nat,
            body: Expr::Add(NumKind::Nat, Box::new(shadow(1)), Box::new(shadow(2))),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        let binders: Vec<String> = body
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Let { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(binders.len(), 2, "got {:?}", body.stmts);
        assert_ne!(binders[0], binders[1], "got {:?}", body.stmts);

        match &body.stmts[2] {
            Stmt::TryLet {
                op: FallibleOp::Arith(_, BinOp::Add, a, b),
                ..
            } => {
                assert_eq!(a, &TExpr::Var(binders[0].clone()));
                assert_eq!(b, &TExpr::Var(binders[1].clone()));
            }
            other => panic!("expected the add, got {:?}", other),
        }
    }

    /// Renaming happens only on an actual collision -- otherwise the generated
    /// code stops looking like the source it came from, and the Task 7 cutover
    /// diff stops being reviewable.
    #[test]
    fn a_let_that_collides_with_nothing_keeps_its_source_name() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("a"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Let(
                String::from("scaled"),
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("scaled"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        assert!(
            matches!(&body.stmts[0], Stmt::Let { name, .. } if name == "scaled"),
            "got {:?}",
            body.stmts
        );
        assert_eq!(
            &body.stmts[1],
            &Stmt::Return(TExpr::Var(String::from("scaled")))
        );
    }

    /// A binder's own value is outside its scope: `let x := x + 1` reads the
    /// OUTER `x` on the right-hand side.
    #[test]
    fn a_binders_value_is_not_in_its_own_scope() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Let(
                String::from("x"),
                Box::new(Expr::Sub(
                    NumKind::Nat,
                    Box::new(Expr::Var(String::from("x"))),
                    Box::new(Expr::Nat(1)),
                )),
                Box::new(Expr::Var(String::from("x"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        match &body.stmts[0] {
            Stmt::Let { name, value, .. } => {
                assert_ne!(name, "x");
                // `Nat.sub` saturates, so this stays a plain BinOp.
                assert!(
                    matches!(value, TExpr::BinOp(_, BinOp::Sub, a, _) if **a == TExpr::Var(String::from("x"))),
                    "the value must read the PARAMETER x, got {:?}",
                    value
                );
            }
            other => panic!("expected the hoisted Let, got {:?}", other),
        }
    }

    /// The invariant this task exists for.
    ///
    /// `if c then (a + b) else 0`. Hoisting the `TryLet` for `a + b` to the
    /// top would evaluate it even when `c` is false -- turning a short-circuit
    /// into eager evaluation and producing an overflow error where Lean has
    /// none. Straight-line lowering cannot see this.
    #[test]
    fn a_fallible_op_in_one_arm_stays_in_that_arm() {
        // `if c then (a + b) else 0`, Nat, Rust profile.
        //
        // Hoisting the TryLet for `a + b` to the top would evaluate it even when
        // `c` is false -- turning a short-circuit into eager evaluation and
        // producing an overflow error where Lean has none.
        let def = Definition {
            name: String::from("f"),
            params: vec![
                (String::from("c"), Type::Bool),
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::If(
                Box::new(Expr::Var(String::from("c"))),
                Box::new(Expr::Add(
                    NumKind::Nat,
                    Box::new(Expr::Var(String::from("a"))),
                    Box::new(Expr::Var(String::from("b"))),
                )),
                Box::new(Expr::Nat(0)),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        // Nothing fallible before the branch.
        for s in &body.stmts {
            if matches!(s, Stmt::If { .. }) {
                break;
            }
            assert!(
                !matches!(s, Stmt::TryLet { .. }),
                "a TryLet was hoisted above the If: {:?}",
                body.stmts
            );
        }
        // And the TryLet is inside the then-branch, not the else.
        let Some(Stmt::If { then, else_, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::If { .. }))
        else {
            panic!("expected an If, got {:?}", body.stmts)
        };
        assert!(
            then.iter().any(|s| matches!(s, Stmt::TryLet { .. })),
            "then: {:?}",
            then
        );
        assert!(
            !else_.iter().any(|s| matches!(s, Stmt::TryLet { .. })),
            "else: {:?}",
            else_
        );
    }

    /// The same invariant, one level down: a `Match` arm is a control-flow
    /// boundary too, and the temporary for `a + b` belongs inside the arm that
    /// asked for it.
    #[test]
    fn a_fallible_op_in_one_match_arm_stays_in_that_arm() {
        // match o with | none => 0 | some _ => a + b
        let def = Definition {
            name: String::from("f"),
            params: vec![
                (String::from("o"), Type::Option(Box::new(Type::Nat))),
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::Match {
                scrut: Box::new(Expr::Var(String::from("o"))),
                alts: vec![
                    Alt {
                        ctor: String::from("Option.none"),
                        binders: vec![],
                        body: Expr::Nat(0),
                    },
                    Alt {
                        ctor: String::from("Option.some"),
                        binders: vec![String::from("v")],
                        body: Expr::Add(
                            NumKind::Nat,
                            Box::new(Expr::Var(String::from("a"))),
                            Box::new(Expr::Var(String::from("b"))),
                        ),
                    },
                ],
                default: None,
            },
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        for s in &body.stmts {
            assert!(
                !matches!(s, Stmt::TryLet { .. }),
                "a TryLet was hoisted above the Switch: {:?}",
                body.stmts
            );
        }
        let Some(Stmt::Switch { arms, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::Switch { .. }))
        else {
            panic!("expected a Switch, got {:?}", body.stmts)
        };
        assert!(
            !arms[0]
                .body
                .iter()
                .any(|s| matches!(s, Stmt::TryLet { .. })),
            "none arm: {:?}",
            arms[0].body
        );
        assert!(
            arms[1]
                .body
                .iter()
                .any(|s| matches!(s, Stmt::TryLet { .. })),
            "some arm: {:?}",
            arms[1].body
        );
    }

    /// A match binder is a source binder like any other, so it goes through
    /// `bind_source` and `scope`.
    ///
    /// Without that, the arm below would bind a second `x` while the
    /// parameter `x` is still live, and the printer's `uses()` -- which counts
    /// reads by NAME, with no scope of its own -- would pool their reads. That
    /// corrupts the decision to fold a single-use temporary, so a shadowing
    /// binder changes the SHAPE of the generated code, not only which value it
    /// reads.
    #[test]
    fn a_match_binder_shadowing_a_parameter_is_renamed() {
        // f(x, o) = match o with | none => x | some x => x
        let def = Definition {
            name: String::from("f"),
            params: vec![
                (String::from("x"), Type::Nat),
                (String::from("o"), Type::Option(Box::new(Type::Nat))),
            ],
            ret: Type::Nat,
            body: Expr::Match {
                scrut: Box::new(Expr::Var(String::from("o"))),
                alts: vec![
                    Alt {
                        ctor: String::from("Option.none"),
                        binders: vec![],
                        body: Expr::Var(String::from("x")),
                    },
                    Alt {
                        ctor: String::from("Option.some"),
                        binders: vec![String::from("x")],
                        body: Expr::Var(String::from("x")),
                    },
                ],
                default: None,
            },
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        let Some(Stmt::Switch { arms, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::Switch { .. }))
        else {
            panic!("expected a Switch, got {:?}", body.stmts)
        };
        // The `none` arm reads the PARAMETER.
        assert_eq!(
            arms[0].body,
            vec![Stmt::Return(TExpr::Var(String::from("x")))]
        );
        // The `some` arm binds its own, renamed, and reads that one.
        let bound = arms[1].binders[0].clone();
        assert_ne!(bound, "x", "the arm binder must be renamed off the param");
        assert_eq!(
            arms[1].body,
            vec![Stmt::Return(TExpr::Var(bound.clone()))],
            "the arm body must read its OWN binder, got {:?}",
            arms[1].body
        );
    }

    /// `Unreachable` is a terminator, not a value.
    #[test]
    fn a_dead_branch_lowers_to_a_fail() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("c"), Type::Bool)],
            ret: Type::Nat,
            body: Expr::If(
                Box::new(Expr::Var(String::from("c"))),
                Box::new(Expr::Nat(1)),
                Box::new(Expr::Unreachable),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        let Some(Stmt::If { then, else_, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::If { .. }))
        else {
            panic!("expected an If, got {:?}", body.stmts)
        };
        assert_eq!(then, &vec![Stmt::Return(TExpr::Lit(Lit::Nat(1)))]);
        assert_eq!(else_, &vec![Stmt::Fail(ErrorCode::Unreachable)]);
    }

    /// `let g := jp g (p) <body>; jmp g arg`, the one join-point form the
    /// corpus contains and the only one this lowering inlines.
    fn def_jp(jp_param: &str, jumps: usize, body: Expr) -> Definition {
        let mut jump: Expr = Expr::Jmp(String::from("g"), vec![Expr::Nat(5)]);
        for _ in 1..jumps {
            jump = Expr::Add(
                NumKind::Nat,
                Box::new(jump),
                Box::new(Expr::Jmp(String::from("g"), vec![Expr::Nat(6)])),
            );
        }
        Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Let(
                String::from("g"),
                Box::new(Expr::Jp {
                    name: String::from("g"),
                    params: vec![String::from(jp_param)],
                    body: Box::new(body),
                }),
                Box::new(jump),
            ),
        }
    }

    /// The single-caller, non-cyclic join point is inlined at its jump site,
    /// and its parameter goes through `bind_source`/`scope` -- so a parameter
    /// name that collides with a definition parameter is renamed, exactly as a
    /// `let` binder would be.
    #[test]
    fn a_single_caller_join_point_inlines_and_its_parameter_is_renamed() {
        // f(x) = let g := jp g (x) (x + 1); jmp g 5
        let def = def_jp(
            "x",
            1,
            Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("x"))),
                Box::new(Expr::Nat(1)),
            ),
        );
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        // The declaration binds nothing: the body moved to the jump site.
        let lets: Vec<&Stmt> = body
            .stmts
            .iter()
            .filter(|s| matches!(s, Stmt::Let { .. }))
            .collect();
        assert_eq!(lets.len(), 1, "got {:?}", body.stmts);
        let Stmt::Let { name, value, .. } = lets[0] else {
            unreachable!()
        };
        assert_ne!(name, "x", "the jp parameter must be renamed off the param");
        assert_eq!(
            value,
            &TExpr::Lit(Lit::Nat(5)),
            "bound to the jump's argument"
        );

        match &body.stmts[1] {
            Stmt::TryLet {
                op: FallibleOp::Arith(_, BinOp::Add, a, _),
                ..
            } => assert_eq!(
                a,
                &TExpr::Var(name.clone()),
                "the jp body must read its OWN parameter, got {:?}",
                a
            ),
            other => panic!("expected the inlined add, got {:?}", other),
        }
    }

    /// A join point with no jump sites is just its body, in place.
    #[test]
    fn a_join_point_nobody_jumps_to_is_its_body() {
        let mut def = def_jp("p", 1, Expr::Nat(7));
        // Replace the jump with a plain value: now `g` has no callers.
        def.body = match def.body {
            Expr::Let(name, value, _) => Expr::Let(name, value, Box::new(Expr::Nat(9))),
            other => other,
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        assert_eq!(
            body.stmts,
            vec![
                Stmt::Let {
                    name: String::from("g"),
                    ty: Type::Nat,
                    value: TExpr::Lit(Lit::Nat(7)),
                },
                Stmt::Return(TExpr::Lit(Lit::Nat(9))),
            ],
            "got {:?}",
            body.stmts
        );
    }

    /// Everything that is not the single-caller, non-cyclic form is rejected,
    /// exactly as `prod-codegen` rejects it today. Widening join-point support
    /// is not part of this plan, and emitting a plausible-looking skeleton for
    /// it is how this project previously shipped Rust that did not compile.
    #[test]
    fn a_multi_caller_or_cyclic_join_point_is_rejected() {
        let two_callers = def_jp("p", 2, Expr::Var(String::from("p")));
        let cyclic = def_jp(
            "p",
            1,
            Expr::Jmp(String::from("g"), vec![Expr::Var(String::from("p"))]),
        );
        for def in [two_callers, cyclic] {
            let defs = vec![def];
            let shapes = signatures(&defs, &TargetProfile::RUST);
            assert_eq!(
                lower_def(&defs[0], &shapes, &TargetProfile::RUST),
                Err(LowerError::UnsupportedJoinPoint(String::from("g"))),
            );
        }
    }

    // -----------------------------------------------------------------------
    // Type declarations, and the rejections that need the type table
    // -----------------------------------------------------------------------

    fn parse(ir: &str) -> prod_ir::Module {
        prod_ir::parser::parse_module(ir).expect("parses").1
    }

    /// The rejection Task 4 had to drop for want of a type table.
    ///
    /// Without it the alternative falls through to the positional pattern and
    /// the printer emits `M.Shape.circle(r, extra)` -- a dotted Lean name used
    /// as a Rust path, with one field too many. That does not compile, and a
    /// generator that emits code which does not compile is strictly worse than
    /// one that names the reason.
    #[test]
    fn a_match_alternative_whose_binder_count_is_wrong_is_rejected() {
        let module = parse(
            r#"(module M (type "M.Shape" (ctor "M.Shape.circle" (r Nat)) (ctor "M.Shape.square" (s Nat))))"#,
        );
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Named(String::from("M.Shape")))],
            ret: Type::Nat,
            body: Expr::Match {
                scrut: Box::new(Expr::Var(String::from("x"))),
                alts: vec![prod_ir::Alt {
                    ctor: String::from("M.Shape.circle"),
                    binders: vec![String::from("r"), String::from("extra")],
                    body: Expr::Var(String::from("r")),
                }],
                default: Some(Box::new(Expr::Nat(0))),
            },
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(
            lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types),
            Err(LowerError::UnsupportedFieldType(String::from(
                "`M.Shape.circle` takes 1 field(s) but got 2 binder(s)"
            ))),
        );

        // And the same alternative with the right number of binders lowers,
        // so the rejection is about the arity rather than about the
        // constructor being declared at all.
        let Expr::Match {
            scrut,
            alts,
            default,
        } = defs[0].body.clone()
        else {
            unreachable!()
        };
        let mut alts = alts;
        alts[0].binders.pop();
        let ok = Definition {
            body: Expr::Match {
                scrut,
                alts,
                default,
            },
            ..defs[0].clone()
        };
        lower_def_in(&ok, &shapes, &TargetProfile::RUST, &module.types)
            .expect("the declared arity lowers");
    }

    /// The same arity question on the construction side. Symmetric with the
    /// alternative above, and rejected in the same words.
    #[test]
    fn a_constructor_applied_to_the_wrong_number_of_arguments_is_rejected() {
        let module = parse(r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#);
        let def = Definition {
            name: String::from("f"),
            params: vec![],
            ret: Type::Named(String::from("M.Pair")),
            body: Expr::Ctor(String::from("M.Pair.mk"), vec![Expr::Nat(1)]),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(
            lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types),
            Err(LowerError::UnsupportedFieldType(String::from(
                "`M.Pair.mk` takes 2 field(s) but got 1 argument(s)"
            ))),
        );
    }

    /// A projection naming a field the declaration does not have. Catches a
    /// declaration and a projection disagreeing within one IR file.
    #[test]
    fn a_projection_of_an_undeclared_field_is_rejected() {
        let module = parse(r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#);
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("p"), Type::Named(String::from("M.Pair")))],
            ret: Type::Nat,
            body: Expr::Proj(
                String::from("M.Pair"),
                String::from("c"),
                Box::new(Expr::Var(String::from("p"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(
            lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types),
            Err(LowerError::UnknownField(
                String::from("M.Pair"),
                String::from("c")
            )),
        );
    }

    /// The rejection KIND when a projection is wrong in two ways at once.
    ///
    /// `(proj "M.Pair" "nope" (opaque "x"))` is both an unknown field and an
    /// opaque operand. The renderer this replaced checked the field BEFORE it
    /// rendered the operand, so it published `UnknownField`; lowering the
    /// operand first silently republishes the same input as `OpaqueExpr`.
    /// The kind is part of the contract, so the order is too.
    #[test]
    fn an_unknown_field_outranks_an_opaque_operand_on_the_body_path() {
        let module = parse(r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#);
        let def = Definition {
            name: String::from("f"),
            params: vec![],
            ret: Type::Nat,
            body: Expr::Proj(
                String::from("M.Pair"),
                String::from("nope"),
                Box::new(Expr::Opaque(String::from("x"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(
            lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types).err(),
            Some(LowerError::UnknownField(
                String::from("M.Pair"),
                String::from("nope")
            )),
        );
    }

    /// The same precedence on the invariant path, which has its own `Proj`
    /// arm and had the same inversion.
    #[test]
    fn an_unknown_field_outranks_an_opaque_operand_on_the_invariant_path() {
        let module = parse(
            r#"
(module M (type "M.Inner" (ctor "M.Inner.mk" (x Nat)))
          (type "M.S" (ctor "M.S.mk" (q (named "M.Inner")))
            (invariant (le 1 (proj "M.Inner" "nope" (opaque "x"))))))
"#,
        );
        assert_eq!(
            lower_types(&module, &crate::names::NamePolicy::RUST).err(),
            Some(LowerError::UnknownField(
                String::from("M.Inner"),
                String::from("nope")
            )),
        );
    }

    /// Every type-declaration rejection `prod-codegen` makes, with the payload
    /// each one carries. The wording is pinned by `REJECTIONS` and by the
    /// published subset contract, so this is a refactor, not a redesign.
    #[test]
    fn the_type_declaration_rejections_keep_their_exact_payloads() {
        let cases: &[(&str, LowerError)] = &[
            (
                r#"(module M (type "M.Poly" (unsupported "type parameters")))"#,
                LowerError::PolymorphicType(String::from("M.Poly")),
            ),
            (
                r#"(module M (type "M.Tree" (unsupported "recursive")))"#,
                LowerError::RecursiveType(String::from("M.Tree")),
            ),
            (
                r#"(module M (type "M.Weird" (unsupported "something else")))"#,
                LowerError::OpaqueType(String::from("M.Weird (something else)")),
            ),
            (
                r#"(module M (type "M.Holder" (ctor "M.Holder.mk" (xs (List Nat)))))"#,
                LowerError::UnsupportedFieldType(String::from(
                    "`M.Holder.xs`: a list field would need owned storage",
                )),
            ),
            (
                r#"(module M (type "M.Holder" (ctor "M.Holder.mk" (xs (Vec Nat)))))"#,
                LowerError::UnsupportedFieldType(String::from(
                    "`M.Holder.xs`: a vector field would need heap storage",
                )),
            ),
            (
                r#"(module M (type "M.Loop" (ctor "M.Loop.mk" (me (named "M.Loop")))))"#,
                LowerError::RecursiveType(String::from("M.Loop")),
            ),
            (
                r#"(module M (type "M.Holder" (ctor "M.Holder.mk" (o (named "M.Missing")))))"#,
                LowerError::OpaqueType(String::from("M.Missing")),
            ),
            (
                r#"(module M (type "A.Instance" (ctor "A.Instance.mk")) (type "B.Instance" (ctor "B.Instance.mk")))"#,
                LowerError::DuplicateTypeName(String::from("Instance")),
            ),
            (
                r#"(module M (type "M.Reserved" (ctor "M.Reserved.mk" (new Nat)) (invariant (le 1 new))))"#,
                LowerError::ReservedFieldName(String::from("M.Reserved"), String::from("new")),
            ),
            (
                r#"(module M (type "M.Two" (ctor "M.Two.a" (x Nat)) (ctor "M.Two.b" (y Nat)) (invariant (le 1 x))))"#,
                LowerError::UnsupportedFieldType(String::from(
                    "`M.Two` carries an invariant but has 2 constructors; only a \
                     single-constructor structure can have one",
                )),
            ),
        ];
        for (ir, expected) in cases {
            let module = parse(ir);
            assert_eq!(
                lower_types(&module, &crate::names::NamePolicy::RUST)
                    .err()
                    .as_ref(),
                Some(expected),
                "for {}",
                ir
            );
        }
    }

    /// The total arithmetic an invariant may contain.
    ///
    /// `Nat` subtraction saturates, so `1 <= q - T` is a single total
    /// expression and the renderer this replaced rendered it. Refusing it would
    /// narrow the published subset for a shape that is entirely plausible in a
    /// Lean-proved structure, so the accepted fragment is the whole total one,
    /// not merely the boolean one.
    #[test]
    fn an_invariant_may_contain_arithmetic_that_cannot_fail() {
        let module = parse(
            r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat) (T Nat) (a U8) (b U8))
                 (invariant (and (le 1 (sub Nat q T)) (le (add U8 a b) 200)))))"#,
        );
        let types = lower_types(&module, &crate::names::NamePolicy::RUST)
            .expect("saturating subtraction and wrapping sized addition are total");
        let invariant = types[0].invariant.as_ref().expect("an invariant");
        // `Nat.sub` saturates and `UInt8.add` wraps; neither is a `TryLet`
        // anywhere, so both stay inside the one expression.
        assert!(
            matches!(
                invariant,
                TExpr::And(a, b)
                    if matches!(&**a, TExpr::BinOp(NumKind::Nat, BinOp::Le, ..))
                    && matches!(&**b, TExpr::BinOp(NumKind::U8, BinOp::Le, ..))
            ),
            "got {:?}",
            invariant
        );
    }

    /// The half of `prod-codegen`'s invariant fragment this lowering
    /// deliberately does NOT keep.
    ///
    /// The renderer this replaced rendered `q * T <= 100` -- `new` returns a
    /// `Result`, so the `?` on `checked_mul` compiled. The result is a checked constructor
    /// that reports `MulOverflow` to a caller whose actual mistake was
    /// violating the invariant. Refusing to generate the type is the better
    /// answer, and it has to be a named rejection, because nothing later is
    /// going to lower it.
    #[test]
    fn an_invariant_containing_a_failing_operation_is_rejected_by_name() {
        for (ir, node) in [
            (
                r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat) (T Nat)) (invariant (le (mul Nat q T) 100))))"#,
                "Mul",
            ),
            (
                r#"(module M (type "M.S" (ctor "M.S.mk" (q Int) (T Int)) (invariant (le (sub Int q T) 100))))"#,
                "Sub",
            ),
            (
                r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat) (T Nat)) (invariant (le (shl Nat q T) 100))))"#,
                "Shl",
            ),
        ] {
            let module = parse(ir);
            assert_eq!(
                lower_types(&module, &crate::names::NamePolicy::RUST).err(),
                Some(LowerError::UnsupportedFieldType(format!(
                    "`M.S`: an invariant may not contain an operation that can fail, and `{}` can; \
                     the checked constructor would report that failure instead of the invariant \
                     it was checking",
                    node
                ))),
                "for {}",
                ir
            );
        }
    }

    /// A deliberate divergence, pinned here because it lands at the Task 7
    /// cutover and a session report is not in the repo.
    ///
    /// `prod-codegen` matches an alternative's `(constructor, arity)` against
    /// its builtin table *before* consulting the declaration, so a module that
    /// declares its own constructor literally named `Nat.succ` gets LCNF's
    /// predecessor rendering regardless of how many fields it declares. The
    /// arity check here consults the declaration unconditionally and rejects.
    /// The rejection is the more correct answer -- the alternative binds one
    /// name for a two-field constructor -- but it is a behaviour change.
    #[test]
    fn a_declared_constructor_shadowing_a_builtin_name_is_still_arity_checked() {
        let module = parse(r#"(module M (type "M.Odd" (ctor "Nat.succ" (a Nat) (b Nat))))"#);
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Named(String::from("M.Odd")))],
            ret: Type::Nat,
            body: Expr::Match {
                scrut: Box::new(Expr::Var(String::from("x"))),
                alts: vec![prod_ir::Alt {
                    ctor: String::from("Nat.succ"),
                    binders: vec![String::from("k")],
                    body: Expr::Var(String::from("k")),
                }],
                default: Some(Box::new(Expr::Nat(0))),
            },
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(
            lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types),
            Err(LowerError::UnsupportedFieldType(String::from(
                "`Nat.succ` takes 2 field(s) but got 1 binder(s)"
            ))),
        );
    }

    /// The construction-side twin of the divergence above.
    ///
    /// The renderer this replaced rendered `Option.some` with one argument as
    /// `Some(x)` before it ever looked the constructor up, so a module declaring its own
    /// two-field `Option.some` silently gets the builtin spelling. Here the
    /// declaration is consulted first and the arity disagreement is named.
    #[test]
    fn a_declared_constructor_shadowing_a_builtin_name_is_arity_checked_on_construction() {
        let module = parse(r#"(module M (type "M.Maybe" (ctor "Option.some" (a Nat) (b Nat))))"#);
        let def = Definition {
            name: String::from("f"),
            params: vec![],
            ret: Type::Named(String::from("M.Maybe")),
            body: Expr::Ctor(String::from("Option.some"), vec![Expr::Nat(1)]),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(
            lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types),
            Err(LowerError::UnsupportedFieldType(String::from(
                "`Option.some` takes 2 field(s) but got 1 argument(s)"
            ))),
        );
    }

    /// An invariant projecting a field its type does not declare.
    ///
    /// This regressed once. Widening the accepted fragment to admit `Proj`
    /// dropped the check the body path was already making, and the result was
    /// worse than the refusal it replaced: `pub fn new(q: crate::Inner) ...
    /// if (1 <= (q).nope)` is generated output that does not compile, where
    /// `prod-codegen` -- whose invariant renderer is built with the module's
    /// type table -- reports `UnknownField`. Both paths now call one function.
    #[test]
    fn an_invariant_projecting_an_undeclared_field_is_rejected() {
        let module = parse(
            r#"
(module M (type "M.Inner" (ctor "M.Inner.mk" (x Nat)))
          (type "M.S" (ctor "M.S.mk" (q (named "M.Inner")))
            (invariant (le 1 (proj "M.Inner" "nope" q)))))
"#,
        );
        assert_eq!(
            lower_types(&module, &crate::names::NamePolicy::RUST).err(),
            Some(LowerError::UnknownField(
                String::from("M.Inner"),
                String::from("nope")
            )),
        );
    }

    /// The other half of the check above: a projection naming a field that
    /// DOES exist still lowers. Without this, the rejection could be satisfied
    /// by refusing every projection, which is the regression it replaced.
    #[test]
    fn an_invariant_projecting_a_declared_field_still_lowers() {
        let module = parse(
            r#"
(module M (type "M.Inner" (ctor "M.Inner.mk" (x Nat)))
          (type "M.S" (ctor "M.S.mk" (q (named "M.Inner")))
            (invariant (le 1 (proj "M.Inner" "x" q)))))
"#,
        );
        let types = lower_types(&module, &crate::names::NamePolicy::RUST)
            .expect("a declared field projects fine");
        let s = types.iter().find(|t| t.lean_name == "M.S").expect("M.S");
        let invariant = s.invariant.as_ref().expect("an invariant");
        assert!(
            matches!(
                invariant,
                TExpr::BinOp(_, BinOp::Le, _, rhs) if matches!(&**rhs, TExpr::Proj(ty, field, _)
                    if ty == "M.Inner" && field == "x")
            ),
            "got {:?}",
            invariant
        );
    }

    /// An invariant is a predicate over fields, so it has no parameters and
    /// every `(param n)` in one is out of bounds. `prod-codegen` builds its
    /// invariant renderer with `params: &[]` and reports exactly this, so the
    /// rejection keeps its own name.
    #[test]
    fn a_parameter_reference_inside_an_invariant_is_out_of_bounds() {
        let module = parse(
            r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat)) (invariant (le 1 (param 0)))))"#,
        );
        assert_eq!(
            lower_types(&module, &crate::names::NamePolicy::RUST).err(),
            Some(LowerError::ParamOutOfBounds(0)),
        );
    }

    // ---------------------------------------------------------------- lists

    /// The corpus definition the list tests are built on: `(List Nat)` in
    /// return position, so `Shape::Buffer`.
    fn corpus_def(name: &str) -> (Module, usize) {
        let module = parse(include_str!("../../../lean/Conformance/golden.ir"));
        let index = module
            .definitions
            .iter()
            .position(|d| d.name.ends_with(name))
            .expect("the definition is in the corpus");
        (module, index)
    }

    fn find_stmt(stmts: &[Stmt], want: &dyn Fn(&Stmt) -> bool) -> bool {
        stmts.iter().any(|s| {
            want(s)
                || match s {
                    Stmt::If { then, else_, .. } => find_stmt(then, want) || find_stmt(else_, want),
                    Stmt::Switch { arms, default, .. } => {
                        arms.iter().any(|a| find_stmt(&a.body, want))
                            || default.as_deref().is_some_and(|d| find_stmt(d, want))
                    }
                    _ => false,
                }
        })
    }

    /// Running out of caller-supplied buffer is a failure, so by this IR's
    /// central invariant it must appear as a statement. It used to live inside
    /// the Rust renderer -- with three printers that is three chances to
    /// forget it.
    ///
    /// The brief's sketch of this test looked for the `Push` at the top level
    /// of `body.stmts`. `c_list_build` opens with a `cases`, so every `Push`
    /// it has is inside a `Switch` arm; the search is recursive here for the
    /// same reason the `OutputTooSmall` search already was.
    #[test]
    fn the_buffer_bounds_check_is_an_explicit_statement_not_the_printers_job() {
        let (module, index) = corpus_def("c_list_build");
        let def = &module.definitions[index];
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        let body = lower_def(def, &shapes, &TargetProfile::RUST).expect("lowers");

        assert_eq!(
            body.shape,
            crate::shape::Shape::Buffer,
            "a (List Nat) return must be Buffer under the Rust profile"
        );
        assert!(
            find_stmt(&body.stmts, &|s| matches!(
                s,
                Stmt::Fail(ErrorCode::OutputTooSmall)
            )),
            "no explicit OutputTooSmall guard in {:?}",
            body.stmts
        );
        assert!(
            find_stmt(&body.stmts, &|s| matches!(s, Stmt::Push { .. })),
            "no Push in {:?}",
            body.stmts
        );
        // The guard is a comparison of the running index against the buffer's
        // length, and it is what the failure hangs off.
        assert!(
            find_stmt(&body.stmts, &|s| matches!(
                s,
                Stmt::If { cond: TExpr::BinOp(_, BinOp::Lt, a, b), else_, .. }
                    if matches!(&**a, TExpr::Seq(SeqQuery::Len, _))
                        && matches!(&**b, TExpr::Seq(SeqQuery::Cap, _))
                        && else_.as_slice() == [Stmt::Fail(ErrorCode::OutputTooSmall)]
            )),
            "the guard is not `len < cap` with the failure in its else-branch: {:?}",
            body.stmts
        );
        // The output sequence is named for the printer, and named through the
        // same binder machinery every other binder uses.
        assert_eq!(body.output.as_deref(), Some("output"));
    }

    /// The same definition under a profile whose lists grow.
    ///
    /// Not a formatting difference: there is no bound to run out of, so the
    /// statement list has a different SHAPE -- the `Push`es are there and the
    /// guard is not. This is the `ListStrategy` seam doing work, and if it
    /// ever passed vacuously the abstraction would have bought nothing.
    #[test]
    fn a_native_sequence_profile_pushes_without_any_bounds_check() {
        let (module, index) = corpus_def("c_list_build");
        let def = &module.definitions[index];
        let shapes = signatures(&module.definitions, &TargetProfile::PYTHON);
        let body = lower_def(def, &shapes, &TargetProfile::PYTHON).expect("lowers");

        assert!(find_stmt(&body.stmts, &|s| matches!(s, Stmt::Push { .. })));
        assert!(
            !find_stmt(&body.stmts, &|s| matches!(
                s,
                Stmt::Fail(ErrorCode::OutputTooSmall)
            )),
            "a growable sequence cannot run out, so nothing may report that it did: {:?}",
            body.stmts
        );
    }

    /// The `sized_mask_required` seam, exercised the way the `ListStrategy`
    /// one above is: the same definition under two profiles, and the
    /// statement trees DIFFER.
    ///
    /// Lean's `UInt8.add` is `BitVec` addition -- it wraps, and the wrap is
    /// the answer, not an overflow. Rust's `u8` wraps by itself, so `RUST`
    /// needs no mask; a host whose integers are unbounded computes
    /// `200 + 100 = 300` where Lean says `44`, so its profile asks for one.
    /// The field used to be declared and read by nothing, which meant a
    /// masking backend would have silently shipped unbounded arithmetic.
    #[test]
    fn a_masking_profile_reduces_a_sized_result_where_the_rust_profile_does_not() {
        let (module, index) = corpus_def("c_u8_add");
        let def = &module.definitions[index];

        let native = lower_def(
            def,
            &signatures(&module.definitions, &TargetProfile::RUST),
            &TargetProfile::RUST,
        )
        .expect("lowers");
        let masked = lower_def(
            def,
            &signatures(&module.definitions, &TargetProfile::PYTHON),
            &TargetProfile::PYTHON,
        )
        .expect("lowers");

        assert_ne!(
            native.stmts, masked.stmts,
            "the masking profile changed nothing, so the seam is not wired"
        );
        // `a + b`, and nothing around it.
        assert!(
            matches!(
                native.stmts.first(),
                Some(Stmt::Let {
                    value: TExpr::BinOp(NumKind::U8, BinOp::Add, ..),
                    ..
                })
            ),
            "expected a bare add under the Rust profile: {:?}",
            native.stmts
        );
        assert!(
            !find_stmt(&native.stmts, &|s| matches!(
                s,
                Stmt::Let {
                    value: TExpr::BinOp(_, BinOp::BitAnd, ..),
                    ..
                }
            )),
            "the Rust profile must not mask -- `u8` already wraps: {:?}",
            native.stmts
        );
        // `(a + b) & 0xff`.
        assert!(
            matches!(
                masked.stmts.first(),
                Some(Stmt::Let {
                    value: TExpr::BinOp(NumKind::U8, BinOp::BitAnd, inner, mask),
                    ..
                }) if matches!(&**inner, TExpr::BinOp(NumKind::U8, BinOp::Add, ..))
                    && **mask == TExpr::Lit(Lit::Nat(255))
            ),
            "expected the add masked to 8 bits: {:?}",
            masked.stmts
        );
    }

    /// `Nat.toUInt8` truncates in Lean (`BitVec` truncation), and Rust's `as`
    /// truncates with it -- so the conversion is a mask on a host where
    /// neither does. Same seam, the other node that narrows.
    #[test]
    fn a_masking_profile_masks_a_narrowing_conversion_too() {
        let (module, index) = corpus_def("c_nat_to_u8");
        let def = &module.definitions[index];

        let native = lower_def(
            def,
            &signatures(&module.definitions, &TargetProfile::RUST),
            &TargetProfile::RUST,
        )
        .expect("lowers");
        let masked = lower_def(
            def,
            &signatures(&module.definitions, &TargetProfile::PYTHON),
            &TargetProfile::PYTHON,
        )
        .expect("lowers");

        assert!(
            matches!(
                native.stmts.first(),
                Some(Stmt::Let {
                    value: TExpr::Convert(NumKind::Nat, NumKind::U8, _),
                    ..
                })
            ),
            "expected a bare conversion under the Rust profile: {:?}",
            native.stmts
        );
        assert!(
            matches!(
                masked.stmts.first(),
                Some(Stmt::Let {
                    value: TExpr::BinOp(NumKind::U8, BinOp::BitAnd, inner, mask),
                    ..
                }) if matches!(&**inner, TExpr::Convert(NumKind::Nat, NumKind::U8, _))
                    && **mask == TExpr::Lit(Lit::Nat(255))
            ),
            "expected the conversion masked to 8 bits: {:?}",
            masked.stmts
        );
    }

    /// A binder introduced BETWEEN a list `let` and the point the list is
    /// consumed must not capture a `Var` inside the deferred expression.
    ///
    /// A list `let` binds nothing at runtime, so its value is re-lowered where
    /// the list is used. That is a different point in the traversal from where
    /// it was written, and `scope` is position-dependent: here the source
    /// writes `let x := ..` after `let xs := [x]`, which `bind_source` renames
    /// (the parameter already holds `x`) and puts in scope. Re-lowering `[x]`
    /// under that scope resolves the element to the RENAMED binder and the
    /// definition computes the wrong list.
    ///
    /// This arm used to rewind only `env`, justified by "LCNF names every
    /// binder uniquely" -- the assumption the uniquification work exists
    /// because we cannot make.
    #[test]
    fn a_binder_between_a_list_let_and_its_use_does_not_capture_the_deferred_list() {
        // f (x : Nat) : List Nat := let xs := [x]; let x := x + 1; xs
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::List(Box::new(Type::Nat)),
            body: Expr::Let(
                String::from("xs"),
                Box::new(Expr::Ctor(
                    String::from("List.cons"),
                    vec![
                        Expr::Var(String::from("x")),
                        Expr::Ctor(String::from("List.nil"), Vec::new()),
                    ],
                )),
                Box::new(Expr::Let(
                    String::from("x"),
                    Box::new(Expr::Add(
                        NumKind::Nat,
                        Box::new(Expr::Var(String::from("x"))),
                        Box::new(Expr::Nat(1)),
                    )),
                    Box::new(Expr::Var(String::from("xs"))),
                )),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        assert_eq!(shapes.get("f"), Some(&Shape::Buffer));
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        // The shadowing `let` really did rename -- otherwise the test would
        // pass because there was nothing to capture.
        let renamed = body
            .stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Let { name, .. } if name != "x" => Some(name.clone()),
                _ => None,
            })
            .expect("the shadowing binder was renamed");
        assert_ne!(renamed, "x");

        // The single element is the PARAMETER, not the later binder.
        let pushed: Vec<&TExpr> = collect_pushed(&body.stmts);
        assert_eq!(
            pushed,
            vec![&TExpr::Var(String::from("x"))],
            "the deferred list element resolved to `{}`, the binder written \
             after the list `let`: {:?}",
            renamed,
            body.stmts
        );
    }

    fn collect_pushed(stmts: &[Stmt]) -> Vec<&TExpr> {
        let mut out = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::Push { value, .. } => out.push(value),
                Stmt::If { then, else_, .. } => {
                    out.extend(collect_pushed(then));
                    out.extend(collect_pushed(else_));
                }
                Stmt::Switch { arms, default, .. } => {
                    for arm in arms {
                        out.extend(collect_pushed(&arm.body));
                    }
                    if let Some(d) = default {
                        out.extend(collect_pushed(d));
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// A list-shaped callee appends to the SAME sequence and reports how many
    /// elements it added.
    ///
    /// The call stays an ordinary `TryLet` -- the callee is the one that can
    /// run out of room -- and the cursor moves in a separate, infallible
    /// `Advance`. Folding the two together would make a second failure point.
    #[test]
    fn a_recursive_list_call_is_a_trylet_and_an_advance_not_a_second_failure_point() {
        let (module, index) = corpus_def("c_list_build");
        let def = &module.definitions[index];
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        let body = lower_def(def, &shapes, &TargetProfile::RUST).expect("lowers");

        assert!(
            find_stmt(&body.stmts, &|s| matches!(
                s,
                Stmt::TryLet { op: FallibleOp::Call(name, args), .. }
                    if name == "c_list_build"
                        && matches!(args.last(), Some(TExpr::Seq(SeqQuery::Rest, _)))
            )),
            "the callee is not handed the unwritten remainder: {:?}",
            body.stmts
        );
        assert!(find_stmt(&body.stmts, &|s| matches!(
            s,
            Stmt::Advance { .. }
        )));
    }

    /// A zero-argument list definition is a promoted `&'static` slice, so it
    /// gets the elements and no bounds check -- there is no caller storage to
    /// run out of.
    #[test]
    fn a_static_list_lowers_to_its_elements_and_nothing_else() {
        let module = parse(
            r#"(module M (def m () (List Nat) (ctor "List.cons" 3 (ctor "List.cons" 5 (ctor "List.nil")))))"#,
        );
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        let body =
            lower_def(&module.definitions[0], &shapes, &TargetProfile::RUST).expect("lowers");
        assert_eq!(body.shape, crate::shape::Shape::StaticList);
        assert!(
            matches!(
                body.stmts.as_slice(),
                [
                    Stmt::Push {
                        value: TExpr::Lit(Lit::Nat(3)),
                        ..
                    },
                    Stmt::Push {
                        value: TExpr::Lit(Lit::Nat(5)),
                        ..
                    },
                    Stmt::Return(TExpr::Seq(SeqQuery::Len, _)),
                ]
            ),
            "got {:?}",
            body.stmts
        );
    }

    /// An array literal can hold constants and nothing else, so a
    /// zero-argument list definition that branches is refused -- in
    /// `prod-codegen`'s own words, and with a rejection that outlives Task 7.
    #[test]
    fn a_static_list_that_is_not_a_constant_chain_is_refused() {
        let module = parse(
            r#"(module M (def m () (List Nat)
                 (if (lt 1 2) (ctor "List.nil") (ctor "List.cons" 1 (ctor "List.nil")))))"#,
        );
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        assert_eq!(
            lower_def(&module.definitions[0], &shapes, &TargetProfile::RUST).err(),
            Some(LowerError::UnsupportedList(String::from(
                "zero-argument list definitions must be constant cons chains"
            )))
        );
    }

    /// The rejections `append` can reach, each in `prod-codegen`'s exact
    /// words.
    ///
    /// The wording is pinned by the published subset contract, so it moves
    /// across the split without being improved. Three of these drifted once
    /// and were restored.
    #[test]
    fn the_list_rejections_keep_prod_codegens_exact_wording() {
        let cases: &[(&str, &str)] = &[
            // A callee that does not write into the caller's buffer.
            (
                r#"(module M (def g ((a Nat)) Nat a) (def m ((a Nat)) (List Nat) (call g a)))"#,
                "`g` does not build its list into a caller buffer",
            ),
            // Something that is not a list at all where a list was declared.
            (
                r#"(module M (def m ((a Nat)) (List Nat) (add Nat a 1)))"#,
                "expression does not build a list",
            ),
            // A name this definition did not bind to a list.
            (
                r#"(module M (def m ((a Nat)) (List Nat) a))"#,
                "`a` is not a list built in this definition",
            ),
            // Shaped like a constant list, but it computes its elements. A
            // DISTINCT reason from the one below, and it must keep its own
            // message rather than collapsing into the generic one.
            (
                r#"(module M (def m () (List Nat) (ctor "List.cons" (add Nat 1 2) (ctor "List.nil"))))"#,
                "`m` computes its list elements, so it cannot be a promoted &'static slice",
            ),
            // Constant elements, but not a chain: an array literal holds
            // neither branches nor anything else.
            (
                r#"(module M (def m () (List Nat)
                     (if (lt 1 2) (ctor "List.nil") (ctor "List.cons" 1 (ctor "List.nil")))))"#,
                "zero-argument list definitions must be constant cons chains",
            ),
        ];
        for (ir, expected) in cases {
            let module = parse(ir);
            let shapes = signatures(&module.definitions, &TargetProfile::RUST);
            let def = module.definitions.last().expect("a definition");
            assert_eq!(
                lower_def_in(def, &shapes, &TargetProfile::RUST, &module.types).err(),
                Some(LowerError::UnsupportedList(String::from(*expected))),
                "for {}",
                ir
            );
        }
    }

    /// Every definition and every type declaration in both IN-REPO corpora
    /// lowers.
    ///
    /// This is the sweep that let `LowerError::NotYetLowered` be deleted: no
    /// corpus definition reached it, so it was scaffolding rather than a
    /// rejection, and the compiler now finds a node with no lowering where a
    /// runtime rejection used to. Pinned on the two corpora a fresh checkout
    /// actually has; `prod-core/kernel.ir` and `prod-core/goldens.ir` are
    /// generated and gitignored, so they cannot be pinned by a test -- they
    /// were swept during the cutover and lower too.
    #[test]
    fn both_in_repo_corpora_lower_completely() {
        let corpora = [
            (
                "golden.ir",
                include_str!("../../../lean/Conformance/golden.ir"),
            ),
            (
                "representative.ir",
                include_str!("../../prod-codegen-compile-tests/fixtures/representative.ir"),
            ),
        ];
        let mut shapes_seen: Vec<Shape> = Vec::new();
        for (label, ir) in corpora {
            let module = parse(ir);
            lower_types(&module, &crate::names::NamePolicy::RUST)
                .unwrap_or_else(|e| panic!("{}: types must lower, got {:?}", label, e));
            let shapes = signatures(&module.definitions, &TargetProfile::RUST);
            assert!(!module.definitions.is_empty(), "{} is empty", label);
            for def in &module.definitions {
                let body = lower_def_in(def, &shapes, &TargetProfile::RUST, &module.types)
                    .unwrap_or_else(|e| {
                        panic!("{}: `{}` must lower, got {:?}", label, def.name, e)
                    });
                shapes_seen.push(body.shape);
            }
        }
        // Not vacuous: the sweep reaches the list shape this task added, not
        // only the shapes that already worked.
        assert!(
            shapes_seen.contains(&Shape::Buffer),
            "the corpora no longer exercise a list-shaped body: {:?}",
            shapes_seen
        );
    }

    /// A list has no by-value form in the allocation-free tier, so a cons cell
    /// outside list position is refused rather than lowered to a `TExpr::Ctor`
    /// no printer can render.
    #[test]
    fn a_list_constructor_outside_list_position_is_refused() {
        let module =
            parse(r#"(module M (def m ((a Nat)) Nat (ctor "List.cons" a (ctor "List.nil"))))"#);
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        assert_eq!(
            lower_def(&module.definitions[0], &shapes, &TargetProfile::RUST).err(),
            Some(LowerError::UnsupportedList(String::from(
                "`List.cons` outside a list return position"
            )))
        );
    }

    // ------------------------------------- comparisons, connectives, casts

    fn body_of(ir: &str) -> Vec<Stmt> {
        let module = parse(ir);
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        lower_def_in(
            &module.definitions[0],
            &shapes,
            &TargetProfile::RUST,
            &module.types,
        )
        .expect("lowers")
        .stmts
    }

    /// A comparison in a definition BODY. `lower_invariant` served the
    /// invariant path from Task 5; `Lowering::expr` had no arm at all, so any
    /// corpus body containing one was refused.
    ///
    /// All four are TOTAL -- none can fail under any profile -- so each is a
    /// `TExpr` and never a `TryLet`, and the operand order is preserved:
    /// `Lt(a, b)` is `a < b`, not `b < a`. A reversed comparison still
    /// compiles and rejects precisely the inputs it should accept.
    #[test]
    fn comparisons_lower_in_a_body_as_total_expressions_in_source_order() {
        for (node, op) in [
            ("eq", BinOp::Eq),
            ("lt", BinOp::Lt),
            ("le", BinOp::Le),
            ("gt", BinOp::Gt),
        ] {
            let stmts = body_of(&format!(
                "(module M (def m ((a Nat) (b Nat)) Bool ({} a b)))",
                node
            ));
            assert!(
                matches!(
                    stmts.as_slice(),
                    [Stmt::Return(TExpr::BinOp(NumKind::Nat, got, x, y))]
                        if *got == op
                            && **x == TExpr::Var(String::from("a"))
                            && **y == TExpr::Var(String::from("b"))
                ),
                "for {}: got {:?}",
                node,
                stmts
            );
        }
    }

    /// A comparison reads its operands at the kind they have, not at `Nat` by
    /// default: `a < 10` over `UInt8` parameters is a `UInt8` comparison.
    #[test]
    fn a_comparison_takes_its_kind_from_the_operand_that_has_one() {
        let stmts = body_of("(module M (def m ((a U8)) Bool (lt a 10)))");
        assert!(
            matches!(
                stmts.as_slice(),
                [Stmt::Return(TExpr::BinOp(NumKind::U8, BinOp::Lt, ..))]
            ),
            "got {:?}",
            stmts
        );
    }

    /// The boolean connectives are total too, so they stay in expression
    /// position.
    #[test]
    fn boolean_connectives_lower_in_a_body() {
        let stmts =
            body_of("(module M (def m ((a Nat) (b Nat)) Bool (and (lt a b) (not (eq a b)))))");
        assert!(
            matches!(
                stmts.as_slice(),
                [Stmt::Return(TExpr::And(x, y))]
                    if matches!(&**x, TExpr::BinOp(_, BinOp::Lt, ..))
                        && matches!(&**y, TExpr::Not(inner)
                            if matches!(&**inner, TExpr::BinOp(_, BinOp::Eq, ..)))
            ),
            "got {:?}",
            stmts
        );

        let stmts = body_of("(module M (def m ((a Nat) (b Nat)) Bool (or (lt a b) (gt a b))))");
        assert!(
            matches!(stmts.as_slice(), [Stmt::Return(TExpr::Or(..))]),
            "got {:?}",
            stmts
        );
    }

    /// `&&` and `||` are LAZY in their right operand, and `TExpr` has no
    /// statement list to hang a lazy operand's work on. Hoisting it would
    /// report an overflow on inputs where Lean -- whose `Nat` is unbounded --
    /// has no failure at all, so it is refused rather than emitted.
    ///
    /// No corpus definition reaches this: the connectives appear in structure
    /// invariants, where a failing operation is already refused outright, and
    /// never in a definition body.
    #[test]
    fn a_connective_whose_right_operand_can_fail_is_refused_not_evaluated_eagerly() {
        let module =
            parse("(module M (def m ((a Nat) (b Nat)) Bool (and (lt a b) (lt (add Nat a b) b))))");
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        assert!(
            matches!(
                lower_def(&module.definitions[0], &shapes, &TargetProfile::RUST).err(),
                Some(LowerError::OpaqueExpr(_))
            ),
            "a hoisted right operand would be a different function"
        );
        // Under a profile whose `Nat` is exact there is nothing to hoist, so
        // the same source lowers.
        let shapes = signatures(&module.definitions, &TargetProfile::PYTHON);
        assert!(lower_def(&module.definitions[0], &shapes, &TargetProfile::PYTHON).is_ok());
    }

    /// The conversion whitelist is the LOSSLESS set and nothing else.
    #[test]
    fn the_lossless_conversions_lower_and_the_rest_are_refused() {
        for (from, to, kind) in [
            ("Nat", "Int", NumKind::Int),
            ("Int", "Nat", NumKind::Nat),
            ("U8", "Nat", NumKind::Nat),
            ("Nat", "U8", NumKind::U8),
            ("U64", "Nat", NumKind::Nat),
            ("Nat", "U32", NumKind::U32),
        ] {
            let stmts = body_of(&format!(
                "(module M (def m ((a {})) {} (convert {} {} a)))",
                from, to, from, to
            ));
            assert!(
                matches!(
                    stmts.as_slice(),
                    [Stmt::Return(TExpr::Convert(_, got, _))] if *got == kind
                ),
                "for {} -> {}: got {:?}",
                from,
                to,
                stmts
            );
        }
    }

    /// Every sized-to-sized pair and every `Int`-to-sized pair is a deliberate
    /// non-goal. They must stay `UnsupportedKind` rather than silently render
    /// a cast that changes the number, and the refusal lives here rather than
    /// in three printers that would each have to remember it.
    #[test]
    fn cross_width_and_int_to_sized_conversions_stay_refused() {
        for (from, to) in [
            ("U8", "U32"),
            ("U32", "U8"),
            ("Int", "U8"),
            ("U8", "Int"),
            ("Nat", "Nat"),
        ] {
            let module = parse(&format!(
                "(module M (def m ((a {})) {} (convert {} {} a)))",
                from, to, from, to
            ));
            let shapes = signatures(&module.definitions, &TargetProfile::RUST);
            assert!(
                matches!(
                    lower_def(&module.definitions[0], &shapes, &TargetProfile::RUST).err(),
                    Some(LowerError::UnsupportedKind(_))
                ),
                "{} -> {} must be refused",
                from,
                to
            );
        }
    }

    /// The invariant path and the body path admit the same conversions,
    /// through the same whitelist. Task 5 found three divergences between
    /// those two paths; this is the check that stops a fourth.
    #[test]
    fn an_invariant_admits_exactly_the_conversions_a_body_does() {
        let module = parse(
            r#"(module M (type "M.S" (ctor "M.S.mk" (used U8))
                 (invariant (le (convert U8 Nat used) 200))))"#,
        );
        let types = lower_types(&module, &crate::names::NamePolicy::RUST)
            .expect("a lossless conversion is total, so an invariant may contain it");
        assert!(
            matches!(
                types[0].invariant.as_ref().expect("an invariant"),
                TExpr::BinOp(NumKind::Nat, BinOp::Le, a, _)
                    if matches!(&**a, TExpr::Convert(NumKind::U8, NumKind::Nat, _))
            ),
            "got {:?}",
            types[0].invariant
        );

        let module = parse(
            r#"(module M (type "M.S" (ctor "M.S.mk" (used U8))
                 (invariant (le (convert U8 U32 used) 200))))"#,
        );
        assert!(
            matches!(
                lower_types(&module, &crate::names::NamePolicy::RUST).err(),
                Some(LowerError::UnsupportedKind(_))
            ),
            "the invariant path must refuse what the body path refuses"
        );
    }

    /// The rejection a whole module's LAST definition produces.
    fn lower_err(ir: &str) -> LowerError {
        let module = parse(ir);
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        let def = module.definitions.last().expect("a definition");
        lower_def_in(def, &shapes, &TargetProfile::RUST, &module.types)
            .expect_err("must be rejected")
    }

    /// The rejection a one-field structure's invariant produces.
    fn invariant_err(invariant: &str) -> LowerError {
        let module = parse(&format!(
            r#"(module M (type "M.S" (ctor "M.S.mk" (q Nat)) {}))"#,
            invariant
        ));
        lower_types(&module, &crate::names::NamePolicy::RUST).expect_err("must be rejected")
    }

    // ------------------------------- Task 7: the rejections that outlive
    //                                 `NotYetLowered`

    /// Deleting `NotYetLowered` orphaned a handful of arms that must still
    /// refuse. Each was mapped onto an EXISTING published rejection rather
    /// than getting a new one, because `REJECTIONS` and
    /// `specs/lean-for-production.md` are pinned -- so what is at risk is not
    /// that a rejection disappears but that it changes KIND, which
    /// `prod-codegen`'s "every variant appears in REJECTIONS" loop cannot
    /// see. This pins the kind for each mapping.
    #[test]
    fn every_arm_that_outlived_not_yet_lowered_kept_a_published_kind() {
        // A lazy connective whose right operand needs statements. `&&` is
        // lazy, and hoisting the operand would report an overflow where Lean
        // has none.
        let ir = "(module M (def m ((a Nat) (b Nat)) Bool (and (lt a b) (lt (add Nat a b) b))))";
        assert!(matches!(lower_err(ir), LowerError::OpaqueExpr(_)));

        // `Opaque` and `Extern` in a definition body: the names
        // `prod-codegen` gave them.
        assert_eq!(
            lower_err(r#"(module M (def m ((a Nat)) Nat (opaque "why")))"#),
            LowerError::OpaqueExpr(String::from("why"))
        );
        assert_eq!(
            lower_err(r#"(module M (def m ((a Nat)) Nat (extern "Foo.helper" a)))"#),
            LowerError::UnresolvedCall(String::from("Foo.helper"))
        );

        // ...and inside an invariant, where they used to degrade.
        assert_eq!(
            invariant_err(r#"(invariant (opaque "why"))"#),
            LowerError::OpaqueExpr(String::from("why"))
        );
        assert_eq!(
            invariant_err(r#"(invariant (extern "Foo.helper" q))"#),
            LowerError::UnresolvedCall(String::from("Foo.helper"))
        );

        // `Jp`, `Jmp` and `Unreachable` inside an invariant. `prod-codegen`
        // renders all three; refusing is a DIVERGENCE, in the safe direction,
        // and none can appear in a Lean-exported invariant. They are named
        // here so the divergence is recorded rather than discovered.
        assert_eq!(
            invariant_err(r#"(invariant (jp g (a) (le 1 q)))"#),
            LowerError::UnsupportedJoinPoint(String::from("g"))
        );
        assert_eq!(
            invariant_err(r#"(invariant (jmp g q))"#),
            LowerError::UnsupportedJoinPoint(String::from("g"))
        );
        assert!(matches!(
            invariant_err(r#"(invariant (unreachable))"#),
            LowerError::OpaqueExpr(_)
        ));
    }

    /// The list rejections carry `UnsupportedList`, not `UnsupportedKind`.
    ///
    /// Both names are separately published, and `From<LowerError>` at the
    /// facade is name-for-name, so it cannot recover one from the other: the
    /// distinction has to exist here or a published rejection silently
    /// changes kind at the cutover.
    #[test]
    fn the_list_rejections_carry_the_list_kind_not_the_numeric_one() {
        for ir in [
            r#"(module M (def g ((a Nat)) Nat a) (def m ((a Nat)) (List Nat) (call g a)))"#,
            r#"(module M (def m ((a Nat)) (List Nat) (add Nat a 1)))"#,
            r#"(module M (def m ((a Nat)) (List Nat) a))"#,
            r#"(module M (def m () (List Nat) (ctor "List.cons" (add Nat 1 2) (ctor "List.nil"))))"#,
            r#"(module M (def m () (List Nat) (if (lt 1 2) (ctor "List.nil") (ctor "List.nil"))))"#,
            r#"(module M (def m ((a Nat)) Nat (ctor "List.cons" a (ctor "List.nil"))))"#,
            r#"(module M (def m ((a Nat)) (Option (List Nat)) (ctor "Option.none")))"#,
        ] {
            assert!(
                matches!(lower_err(ir), LowerError::UnsupportedList(_)),
                "must be UnsupportedList, got {:?} for {}",
                lower_err(ir),
                ir
            );
        }
    }

    /// A signature's types are checked HERE, before the body is lowered.
    ///
    /// Nothing downstream can refuse one: `prod-emit-rust` is total by
    /// construction and renders an unrenderable type as a placeholder
    /// identifier rather than an error. `prod-codegen` refused these in
    /// `param_type_to_rust`/`type_to_rust`, and the rejections came across
    /// with it.
    #[test]
    fn a_signature_type_with_no_rendering_is_refused_before_the_body_is() {
        assert_eq!(
            lower_err(r#"(module M (def m ((x (named "M.Nope"))) Nat 0))"#),
            LowerError::OpaqueType(String::from("M.Nope"))
        );
        assert_eq!(
            lower_err(r#"(module M (def m ((x Nat)) (named "M.Nope") x))"#),
            LowerError::OpaqueType(String::from("M.Nope"))
        );
        assert_eq!(
            lower_err(r#"(module M (def m ((x (opaque "Foo.Bar"))) Nat 0))"#),
            LowerError::OpaqueType(String::from("Foo.Bar"))
        );
        assert_eq!(
            lower_err(r#"(module M (def m ((xs (Vec Nat))) Nat 0))"#),
            LowerError::HeapType(String::from("(Vec Nat)"))
        );
        assert_eq!(
            lower_err(r#"(module M (def m ((xs (Option (List Nat)))) Nat 0))"#),
            LowerError::UnsupportedList(String::from(
                "(List Nat) is only supported directly as a parameter or return type"
            ))
        );
    }

    /// A type that trips BOTH signature checks reports the undeclared name,
    /// not the container.
    ///
    /// The order is `prod-codegen`'s: `check_named_type` ran first and recursed
    /// through `Vec` and `List`, so `(Vec (named "M.Nope"))` was
    /// `OpaqueType`, not `HeapType`. Both kinds are separately published, so
    /// the two checks running in the other order would silently change which
    /// one a caller sees. Pathological input, pinned anyway -- it is exactly
    /// the kind of thing a port loses without anyone noticing.
    #[test]
    fn an_undeclared_name_inside_an_unrenderable_container_reports_the_name() {
        assert_eq!(
            lower_err(r#"(module M (def m ((xs (Vec (named "M.Nope")))) Nat 0))"#),
            LowerError::OpaqueType(String::from("M.Nope"))
        );
        assert_eq!(
            lower_err(r#"(module M (def m ((xs (List (List (named "M.Nope"))))) Nat 0))"#),
            LowerError::OpaqueType(String::from("M.Nope"))
        );
        // ...and with the name declared, the container is what is reported.
        assert_eq!(
            lower_err(
                r#"(module M (type "M.Ok" (ctor "M.Ok.mk" (a Nat)))
                     (def m ((xs (Vec (named "M.Ok")))) Nat 0))"#
            ),
            LowerError::HeapType(String::from("(Vec (named \"M.Ok\"))"))
        );
    }

    /// A dotted constructor the module does not declare is refused, not
    /// rendered: a Lean name is not a target path in expression position, so
    /// `Conformance.NoProp.mk(n, n)` would surface as a compiler error far
    /// from the IR that caused it. A dot-free name is at least a syntactically
    /// valid path to something the host may supply by hand, so it survives --
    /// exactly `prod-codegen`'s split.
    #[test]
    fn an_undeclared_dotted_constructor_is_unresolved_but_a_bare_one_is_not() {
        assert_eq!(
            lower_err(r#"(module M (def m ((n Nat)) Nat (ctor "Conformance.NoProp.mk" n n)))"#),
            LowerError::UnresolvedCall(String::from("Conformance.NoProp.mk"))
        );
        let module = parse(r#"(module M (def m ((n Nat)) Nat (ctor "Pair" n 2)))"#);
        let shapes = signatures(&module.definitions, &TargetProfile::RUST);
        assert!(lower_def_in(
            &module.definitions[0],
            &shapes,
            &TargetProfile::RUST,
            &module.types
        )
        .is_ok());
    }
}
