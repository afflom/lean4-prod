//! nom-based parser for the Lean 4 → prod compact IR format
//!
//! Grammar (simplified sexp):
//! ```text
//! module   ::= "(" "module" ident type_decl* def* ")"
//! type_decl ::= "(" "type" '"' ident '"' unsupported? ctor_decl* ")"
//! unsupported ::= "(" "unsupported" '"' text '"' ")"
//! ctor_decl ::= "(" "ctor" '"' ident '"' field* ")"
//! field    ::= "(" ident type ")"
//! def      ::= "(" "def" ident "(" param* ")" type expr ")"
//! param    ::= "(" ident type ")"
//! kind     ::= "Nat" | "Int" | "U8" | "U16" | "U32" | "U64"  ; numeric kind tag
//! type     ::= "Nat" | "Int" | "Bool" | "(" "Option" type ")" | "(" "Vec" type ")"
//!            | "(" "List" type ")" | "(" "Tuple" type* ")" | "(" "named" '"' ident '"' ")"
//!            | "(" "opaque" '"' ident '"' ")"
//! expr     ::= nat | ident | "(" "param" nat ")"
//!            | "(" "add" kind expr expr ")" | "(" "sub" kind expr expr ")"
//!            | "(" "mul" kind expr expr ")" | "(" "div" kind expr expr ")"
//!            | "(" "mod" kind expr expr ")" | "(" "shl" kind expr expr ")"
//!            | "(" "shr" kind expr expr ")" | "(" "pow" kind expr expr ")"
//!            | "(" "neg" kind expr ")"
//!            | "(" "convert" kind kind expr ")"              ; numeric-kind conversion
//!            | "(" "opaque" '"' ident '"' ")"
//!            | "(" "eq" expr expr ")" | "(" "lt" expr expr ")" | "(" "le" expr expr ")"
//!            | "(" "gt" expr expr ")" | "(" "if" expr expr expr ")" | "(" "let" ident expr expr ")"
//!            | "(" "call" ident expr* ")"
//!            | "(" "cases" expr alt* default? ")"          ; LCNF cases_on
//!            | "(" "ctor" '"' ident '"' expr* ")"          ; constructor application
//!            | "(" "proj" '"' ident '"' '"' ident '"' expr ")"  ; structure projection
//!            | "(" "jp" ident "(" ident* ")" expr ")"      ; LCNF join point
//!            | "(" "jmp" ident expr* ")"                   ; LCNF jump
//!            | "(" "unreachable" ")"
//!            | "(" "extern" '"' ident '"' expr* ")"        ; unresolved callee
//! alt      ::= "(" "alt" '"' ident '"' "(" ident* ")" expr ")"
//! default  ::= "(" "default" expr ")"
//! comment  ::= ";;" ... end-of-line                       ; skipped as whitespace
//! ```

use super::{Alt, CtorDecl, Definition, Expr, Module, NumKind, Type, TypeDecl};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till, take_while1},
    character::complete::{char, digit1, multispace1},
    combinator::{map, map_res, opt, value},
    multi::many0,
    sequence::{delimited, preceded, terminated, tuple},
    IResult,
};

/// Whitespace, including Lisp-style `;;` line comments (skipped everywhere)
fn space_and_comments(input: &str) -> IResult<&str, ()> {
    value(
        (),
        many0(alt((
            value((), multispace1),
            value((), preceded(tag(";;"), take_till(|c| c == '\n'))),
        ))),
    )(input)
}

fn ws<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(space_and_comments, inner, space_and_comments)
}

fn ident(input: &str) -> IResult<&str, String> {
    map(
        take_while1(|c: char| c.is_alphanumeric() || c == '_' || c == '-' || c == '.'),
        String::from,
    )(input)
}

fn quoted_ident(input: &str) -> IResult<&str, String> {
    delimited(char('"'), ident, char('"'))(input)
}

fn parse_u64(input: &str) -> IResult<&str, u64> {
    map_res(digit1, |s: &str| s.parse::<u64>())(input)
}

fn parse_i64(input: &str) -> IResult<&str, i64> {
    // Parse the magnitude in `i128` and apply the sign before narrowing:
    // `"9223372036854775808"` is not a valid `i64` on its own, yet
    // `-9223372036854775808` is `i64::MIN`. Parsing the digits as `i64` and
    // negating afterwards would reject that literal (and, before the digits
    // widened, panicked on the `unwrap`). Out-of-range values fail the parser
    // rather than wrapping or aborting.
    map_res(
        tuple((opt(char('-')), digit1)),
        |(neg, digits): (Option<char>, &str)| {
            let magnitude = digits.parse::<i128>().map_err(|_| ())?;
            let signed = if neg.is_some() { -magnitude } else { magnitude };
            i64::try_from(signed).map_err(|_| ())
        },
    )(input)
}

/// `U8 | U16 | U32 | U64` — the sized-integer type tag. Deliberately
/// distinct from `parse_num_kind`: it excludes `Nat`/`Int`, so
/// `Type::UInt(NumKind::Nat)`/`Type::UInt(NumKind::Int)` are unrepresentable
/// rather than parseable-then-rejected.
fn parse_sized_kind(input: &str) -> IResult<&str, NumKind> {
    ws(alt((
        value(NumKind::U8, tag("U8")),
        value(NumKind::U16, tag("U16")),
        value(NumKind::U32, tag("U32")),
        value(NumKind::U64, tag("U64")),
    )))(input)
}

fn parse_type(input: &str) -> IResult<&str, Type> {
    ws(alt((
        value(Type::Nat, tag("Nat")),
        value(Type::Int, tag("Int")),
        value(Type::Bool, tag("Bool")),
        map(parse_sized_kind, Type::UInt),
        map(
            delimited(char('('), tuple((tag("Option"), parse_type)), char(')')),
            |(_, t)| Type::Option(Box::new(t)),
        ),
        map(
            delimited(char('('), tuple((tag("Vec"), parse_type)), char(')')),
            |(_, t)| Type::Vec(Box::new(t)),
        ),
        map(
            delimited(char('('), tuple((tag("List"), parse_type)), char(')')),
            |(_, t)| Type::List(Box::new(t)),
        ),
        map(
            delimited(
                char('('),
                tuple((tag("Tuple"), many0(parse_type))),
                char(')'),
            ),
            |(_, ts)| Type::Tuple(ts),
        ),
        map(
            delimited(
                char('('),
                tuple((tag("named"), ws(quoted_ident))),
                char(')'),
            ),
            |(_, n)| Type::Named(n),
        ),
        map(
            delimited(
                char('('),
                tuple((tag("opaque"), ws(quoted_ident))),
                char(')'),
            ),
            |(_, s)| Type::Opaque(s),
        ),
    )))(input)
}

fn parse_param(input: &str) -> IResult<&str, (String, Type)> {
    delimited(char('('), tuple((ws(ident), ws(parse_type))), char(')'))(input)
}

/// `(binders...)` — a parenthesized list of bare identifiers
fn parse_binders(input: &str) -> IResult<&str, Vec<String>> {
    delimited(char('('), many0(ws(ident)), char(')'))(input)
}

/// `(alt "CtorName" (binders...) <body>)`
fn parse_alt(input: &str) -> IResult<&str, Alt> {
    map(
        delimited(
            char('('),
            tuple((
                tag("alt"),
                ws(quoted_ident),
                ws(parse_binders),
                ws(parse_expr),
            )),
            char(')'),
        ),
        |(_, ctor, binders, body)| Alt {
            ctor,
            binders,
            body,
        },
    )(input)
}

/// `Nat | Int | U8 | U16 | U32 | U64` — the numeric kind tag on an
/// arithmetic node. No prefix collisions among these, so no delimiter guard
/// is needed (unlike `le`, which prefix-matches `let`).
fn parse_num_kind(input: &str) -> IResult<&str, NumKind> {
    ws(alt((
        value(NumKind::Nat, tag("Nat")),
        value(NumKind::Int, tag("Int")),
        value(NumKind::U8, tag("U8")),
        value(NumKind::U16, tag("U16")),
        value(NumKind::U32, tag("U32")),
        value(NumKind::U64, tag("U64")),
    )))(input)
}

/// `(default <body>)`
fn parse_default(input: &str) -> IResult<&str, Expr> {
    map(
        delimited(
            char('('),
            tuple((tag("default"), ws(parse_expr))),
            char(')'),
        ),
        |(_, body)| body,
    )(input)
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    ws(alt((
        map(parse_u64, Expr::Nat),
        map(parse_i64, Expr::Int),
        map(tag("true"), |_| Expr::Bool(true)),
        map(tag("false"), |_| Expr::Bool(false)),
        parse_paren_expr,
        map(ident, Expr::Var),
    )))(input)
}

/// All parenthesized expression forms, dispatched on the leading keyword.
/// Split into two `alt` groups to stay within nom's tuple arity limit.
fn parse_paren_expr(input: &str) -> IResult<&str, Expr> {
    delimited(
        char('('),
        ws(alt((
            alt((
                map(tuple((tag("param"), ws(parse_u64))), |(_, idx)| {
                    Expr::Param(idx as usize)
                }),
                map(
                    tuple((tag("add"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Add(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("sub"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Sub(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("mul"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Mul(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("div"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Div(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("mod"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Mod(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("shl"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Shl(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("shr"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Shr(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("pow"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Pow(k, Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("neg"), parse_num_kind, ws(parse_expr))),
                    |(_, k, a)| Expr::Neg(k, Box::new(a)),
                ),
                map(
                    tuple((tag("eq"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Eq(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("lt"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Lt(Box::new(a), Box::new(b)),
                ),
                map(
                    // `le` must be delimiter-terminated: bare `tag("le")`
                    // prefix-matches the `let` keyword and derails the
                    // enclosing alt (no backtracking reaches `let`).
                    tuple((
                        terminated(tag("le"), multispace1),
                        ws(parse_expr),
                        ws(parse_expr),
                    )),
                    |(_, a, b)| Expr::Le(Box::new(a), Box::new(b)),
                ),
            )),
            alt((
                map(
                    tuple((tag("gt"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Gt(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((
                        tag("convert"),
                        parse_num_kind,
                        parse_num_kind,
                        ws(parse_expr),
                    )),
                    |(_, from, to, e)| Expr::Convert(from, to, Box::new(e)),
                ),
                map(
                    tuple((tag("if"), ws(parse_expr), ws(parse_expr), ws(parse_expr))),
                    |(_, cond, t, f)| Expr::If(Box::new(cond), Box::new(t), Box::new(f)),
                ),
                map(
                    tuple((tag("let"), ws(ident), ws(parse_expr), ws(parse_expr))),
                    |(_, name, val, body)| Expr::Let(name, Box::new(val), Box::new(body)),
                ),
                map(
                    tuple((tag("call"), ws(ident), many0(ws(parse_expr)))),
                    |(_, name, args)| Expr::Call(name, args),
                ),
                map(
                    tuple((
                        tag("cases"),
                        ws(parse_expr),
                        many0(ws(parse_alt)),
                        opt(ws(parse_default)),
                    )),
                    |(_, scrut, alts, default)| Expr::Match {
                        scrut: Box::new(scrut),
                        alts,
                        default: default.map(Box::new),
                    },
                ),
                map(
                    tuple((tag("ctor"), ws(quoted_ident), many0(ws(parse_expr)))),
                    |(_, name, args)| Expr::Ctor(name, args),
                ),
                map(
                    tuple((
                        tag("proj"),
                        ws(quoted_ident),
                        ws(quoted_ident),
                        ws(parse_expr),
                    )),
                    |(_, ty, field, e)| Expr::Proj(ty, field, Box::new(e)),
                ),
                map(
                    tuple((tag("jp"), ws(ident), ws(parse_binders), ws(parse_expr))),
                    |(_, name, params, body)| Expr::Jp {
                        name,
                        params,
                        body: Box::new(body),
                    },
                ),
                map(
                    tuple((tag("jmp"), ws(ident), many0(ws(parse_expr)))),
                    |(_, name, args)| Expr::Jmp(name, args),
                ),
                map(tag("unreachable"), |_| Expr::Unreachable),
                map(tuple((tag("opaque"), ws(quoted_ident))), |(_, s)| {
                    Expr::Opaque(s)
                }),
                map(
                    tuple((tag("extern"), ws(quoted_ident), many0(ws(parse_expr)))),
                    |(_, name, args)| Expr::Extern(name, args),
                ),
            )),
        ))),
        ws(char(')')),
    )(input)
}

/// `(name Type)` — one field of a constructor declaration.
fn parse_field(input: &str) -> IResult<&str, (String, Type)> {
    delimited(char('('), tuple((ws(ident), ws(parse_type))), char(')'))(input)
}

/// `(ctor "Full.Name.mk" (field Type)...)`
fn parse_ctor_decl(input: &str) -> IResult<&str, CtorDecl> {
    map(
        delimited(
            char('('),
            tuple((tag("ctor"), ws(quoted_ident), many0(ws(parse_field)))),
            char(')'),
        ),
        |(_, name, fields)| CtorDecl { name, fields },
    )(input)
}

/// `(unsupported "reason")` — a type the exporter reached but cannot describe.
fn parse_unsupported(input: &str) -> IResult<&str, String> {
    delimited(
        char('('),
        map(tuple((tag("unsupported"), ws(quoted_reason))), |(_, r)| r),
        char(')'),
    )(input)
}

/// A double-quoted free-text reason (unlike `quoted_ident`, spaces allowed).
fn quoted_reason(input: &str) -> IResult<&str, String> {
    delimited(
        char('"'),
        map(take_till(|c| c == '"'), String::from),
        char('"'),
    )(input)
}

/// `(type "Full.Name" (ctor ...)...)` or `(type "Full.Name" (unsupported "why"))`
fn parse_type_decl(input: &str) -> IResult<&str, TypeDecl> {
    map(
        delimited(
            char('('),
            tuple((
                terminated(tag("type"), multispace1),
                ws(quoted_ident),
                opt(ws(parse_unsupported)),
                many0(ws(parse_ctor_decl)),
            )),
            char(')'),
        ),
        |(_, name, unsupported, ctors)| TypeDecl {
            name,
            ctors,
            unsupported,
        },
    )(input)
}

fn parse_definition(input: &str) -> IResult<&str, Definition> {
    let (rest, (_, name, params, ret, body)) = delimited(
        char('('),
        tuple((
            tag("def"),
            ws(ident),
            delimited(char('('), many0(ws(parse_param)), char(')')),
            ws(parse_type),
            ws(parse_expr),
        )),
        char(')'),
    )(input)?;

    Ok((
        rest,
        Definition {
            name,
            params,
            ret,
            body,
        },
    ))
}

pub fn parse_module(input: &str) -> IResult<&str, Module> {
    let (rest, (_, name, types, definitions)) = ws(delimited(
        char('('),
        tuple((
            tag("module"),
            ws(ident),
            many0(ws(parse_type_decl)),
            many0(ws(parse_definition)),
        )),
        char(')'),
    ))(input)?;

    Ok((
        rest,
        Module {
            name,
            types,
            definitions,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;

    #[test]
    fn test_parse_type_nat() {
        assert_eq!(parse_type("Nat"), Ok(("", Type::Nat)));
    }

    #[test]
    fn test_parse_type_list() {
        assert_eq!(
            parse_type("(List Nat)"),
            Ok(("", Type::List(Box::new(Type::Nat))))
        );
        assert_eq!(
            parse_type("(List (Tuple Nat Nat))"),
            Ok((
                "",
                Type::List(Box::new(Type::Tuple(alloc::vec![Type::Nat, Type::Nat])))
            ))
        );
    }

    #[test]
    fn test_parse_le() {
        let (rest, expr) = parse_expr("(le (param 0) 10)").unwrap();
        assert!(rest.is_empty());
        assert!(matches!(expr, Expr::Le(_, _)));
    }

    #[test]
    fn test_parse_le_does_not_eat_let() {
        // Regression: bare `tag("le")` prefix-matches `let`.
        let (rest, expr) = parse_expr("(let x 1 x)").unwrap();
        assert!(rest.is_empty());
        assert!(matches!(expr, Expr::Let(_, _, _)));
    }

    #[test]
    fn test_parse_i64_extremes_do_not_panic() {
        // Regression: parsing the magnitude as `i64` and negating afterwards
        // panicked on `i64::MIN`'s digit string.
        assert_eq!(
            parse_expr("-9223372036854775808"),
            Ok(("", Expr::Int(i64::MIN)))
        );
        assert_eq!(parse_expr("-1"), Ok(("", Expr::Int(-1))));
        // Non-negative literals still parse as `Nat` (the `u64` branch wins).
        assert_eq!(
            parse_expr("9223372036854775807"),
            Ok(("", Expr::Nat(i64::MAX as u64)))
        );
    }

    #[test]
    fn test_parse_i64_out_of_range_is_rejected_not_wrapped() {
        // One past `i64::MIN`: the magnitude fits `i128` but not `i64`.
        assert!(parse_i64("-9223372036854775809").is_err());
    }

    #[test]
    fn test_parse_expr_add() {
        let input =
            r#"(add Nat (mul Nat (param 0) (proj "UorAtlas.Instance" "O" (param 1))) (param 2))"#;
        let (rest, expr) = parse_expr(input).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Add(_, _, _) => {}
            _ => panic!("Expected Add, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_class_index() {
        let input = r#"
(module UorAtlas.Kernel
  (def classIndex ((h2 Nat) (d Nat) (l Nat) (inst (named "UorAtlas.Instance"))) Nat
    (add Nat (mul Nat (call stride inst) h2)
         (add Nat (mul Nat (proj "UorAtlas.Instance" "O" inst) d) l)))
)
"#;
        let (rest, module) = parse_module(input).unwrap();
        assert!(rest.trim().is_empty());
        assert_eq!(module.name, "UorAtlas.Kernel");
        assert_eq!(module.definitions.len(), 1);
        assert_eq!(module.definitions[0].name, "classIndex");
    }

    #[test]
    fn test_parse_line_comment() {
        let input = ";; header comment\n(module M ;; trailing comment\n)";
        let (rest, module) = parse_module(input).unwrap();
        assert!(rest.trim().is_empty());
        assert_eq!(module.name, "M");
    }

    #[test]
    fn test_parse_cases() {
        let input = r#"(cases (param 0)
            (alt "Some" (v) v)
            (alt "Pair" (a b) (add Nat a b))
            (default 0))"#;
        let (rest, expr) = parse_expr(input).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Match {
                scrut,
                alts,
                default,
            } => {
                assert!(matches!(*scrut, Expr::Param(0)));
                assert_eq!(alts.len(), 2);
                assert_eq!(alts[0].ctor, "Some");
                assert_eq!(alts[0].binders, vec!["v"]);
                assert_eq!(alts[1].binders, vec!["a", "b"]);
                assert!(matches!(default.as_deref(), Some(Expr::Nat(0))));
            }
            _ => panic!("Expected Match, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_ctor() {
        let (rest, expr) = parse_expr(r#"(ctor "Pair" 1 2)"#).unwrap();
        assert!(rest.is_empty());
        assert_eq!(
            expr,
            Expr::Ctor("Pair".into(), vec![Expr::Nat(1), Expr::Nat(2)])
        );
    }

    #[test]
    fn test_parse_proj() {
        let (rest, expr) = parse_expr(r#"(proj "Pair" "fst" (ctor "Pair" 1 2))"#).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Proj(ty, field, e) => {
                assert_eq!(ty, "Pair");
                assert_eq!(field, "fst");
                assert!(matches!(*e, Expr::Ctor(..)));
            }
            _ => panic!("Expected Proj, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_jp_jmp() {
        let (rest, expr) =
            parse_expr(r#"(jp loop (i acc) (if (lt i 10) (jmp loop (add Nat i 1) acc) acc))"#)
                .unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Jp { name, params, body } => {
                assert_eq!(name, "loop");
                assert_eq!(params, vec!["i", "acc"]);
                assert!(matches!(*body, Expr::If(..)));
            }
            _ => panic!("Expected Jp, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_unreachable() {
        let (rest, expr) = parse_expr("(unreachable)").unwrap();
        assert!(rest.is_empty());
        assert_eq!(expr, Expr::Unreachable);
    }

    #[test]
    fn test_parse_shr() {
        let (rest, expr) = parse_expr("(shr Nat n 1)").unwrap();
        assert!(rest.is_empty());
        assert!(matches!(expr, Expr::Shr(..)));
    }

    #[test]
    fn test_parse_gt() {
        let (rest, expr) = parse_expr("(gt (param 0) 1)").unwrap();
        assert!(rest.is_empty());
        assert!(matches!(expr, Expr::Gt(..)));
    }

    #[test]
    fn test_parse_pow() {
        let (rest, expr) =
            parse_expr("(pow Nat 2 (sub Nat (proj \"Instance\" \"o\" i) 1))").unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Pow(k, a, b) => {
                assert_eq!(k, NumKind::Nat);
                assert_eq!(*a, Expr::Nat(2));
                assert!(matches!(*b, Expr::Sub(..)));
            }
            _ => panic!("Expected Pow, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_opaque_expr() {
        let (rest, expr) = parse_expr(r#"(opaque "f1-closure")"#).unwrap();
        assert!(rest.is_empty());
        assert_eq!(expr, Expr::Opaque("f1-closure".into()));
    }

    #[test]
    fn test_parse_opaque_type() {
        let (rest, ty) = parse_type(r#"(opaque "Foo.Bar")"#).unwrap();
        assert!(rest.is_empty());
        assert_eq!(ty, Type::Opaque("Foo.Bar".into()));
    }

    #[test]
    fn test_parse_type_decl_single_ctor() {
        let input = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
)
"#;
        let (rest, module) = parse_module(input).unwrap();
        assert!(rest.trim().is_empty());
        assert_eq!(module.types.len(), 1);
        assert_eq!(module.types[0].name, "UorAtlas.Instance");
        assert_eq!(module.types[0].ctors.len(), 1);
        assert_eq!(module.types[0].ctors[0].name, "UorAtlas.Instance.mk");
        assert_eq!(
            module.types[0].ctors[0].fields,
            vec![
                ("q".to_string(), Type::Nat),
                ("T".to_string(), Type::Nat),
                ("O".to_string(), Type::Nat),
            ]
        );
    }

    #[test]
    fn test_parse_type_decl_multi_ctor_and_named_type() {
        let input = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat)))
  (def area ((s (named "M.Shape"))) Nat 0)
)
"#;
        let (rest, module) = parse_module(input).unwrap();
        assert!(rest.trim().is_empty());
        assert_eq!(module.types[0].ctors.len(), 2);
        assert_eq!(module.types[0].ctors[1].fields.len(), 2);
        assert_eq!(
            module.definitions[0].params[0].1,
            Type::Named("M.Shape".to_string())
        );
    }

    #[test]
    fn test_parse_ctor_with_no_fields() {
        let input = r#"(module M (type "M.Unit" (ctor "M.Unit.mk")))"#;
        let (_, module) = parse_module(input).unwrap();
        assert!(module.types[0].ctors[0].fields.is_empty());
    }

    #[test]
    fn test_parse_extern() {
        let (rest, expr) = parse_expr(r#"(extern "Foo.bar" 1 2)"#).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Extern(name, args) => {
                assert_eq!(name, "Foo.bar");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Extern, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_unsupported_type_decl() {
        let input = r#"(module M (type "M.Poly" (unsupported "type parameters")))"#;
        let (_, module) = parse_module(input).unwrap();
        assert_eq!(
            module.types[0].unsupported.as_deref(),
            Some("type parameters")
        );
        assert!(module.types[0].ctors.is_empty());
    }

    #[test]
    fn test_parse_kind_tagged_arithmetic() {
        let (rest, expr) = parse_expr("(add Nat a b)").unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Add(kind, _, _) => assert_eq!(kind, NumKind::Nat),
            _ => panic!("expected Add, got {:?}", expr),
        }
        assert!(matches!(
            parse_expr("(mul Int a b)").unwrap().1,
            Expr::Mul(NumKind::Int, _, _)
        ));
        assert!(matches!(
            parse_expr("(sub U8 a b)").unwrap().1,
            Expr::Sub(NumKind::U8, _, _)
        ));
    }

    #[test]
    fn test_parse_every_num_kind() {
        for (text, expected) in [
            ("Nat", NumKind::Nat),
            ("Int", NumKind::Int),
            ("U8", NumKind::U8),
            ("U16", NumKind::U16),
            ("U32", NumKind::U32),
            ("U64", NumKind::U64),
        ] {
            let ir = alloc::format!("(add {} a b)", text);
            match parse_expr(&ir).unwrap().1 {
                Expr::Add(kind, _, _) => assert_eq!(kind, expected, "for {}", text),
                other => panic!("expected Add for {}, got {:?}", text, other),
            }
        }
    }

    #[test]
    fn test_untagged_arithmetic_no_longer_parses() {
        // The tag is mandatory. An untagged node would have to mean something by
        // default, and "add means Nat" implicitly is exactly what this removes.
        // No arm of `parse_paren_expr` matches `(add a b)` once `add` requires a
        // kind, so the whole expression fails rather than parsing as something
        // else.
        assert!(parse_expr("(add a b)").is_err());
    }

    #[test]
    fn test_parse_neg() {
        match parse_expr("(neg Int a)").unwrap().1 {
            Expr::Neg(kind, _) => assert_eq!(kind, NumKind::Int),
            other => panic!("expected Neg, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_convert() {
        let (rest, expr) = parse_expr("(convert Nat Int a)").unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Convert(from, to, e) => {
                assert_eq!(from, NumKind::Nat);
                assert_eq!(to, NumKind::Int);
                assert!(matches!(*e, Expr::Var(_)));
            }
            other => panic!("expected Convert, got {:?}", other),
        }
    }

    #[test]
    fn test_comparisons_are_not_kind_tagged() {
        // Both operands share a Rust type and `<` works for every kind, so a tag
        // here would be noise.
        assert!(matches!(parse_expr("(lt a b)").unwrap().1, Expr::Lt(_, _)));
    }
}
