//! nom-based parser for the Lean 4 → prod compact IR format
//!
//! Grammar (simplified sexp):
//! ```text
//! module   ::= "(" "module" ident def* ")"
//! def      ::= "(" "def" ident "(" param* ")" type expr ")"
//! param    ::= "(" ident type ")"
//! type     ::= "Nat" | "Int" | "Bool" | "Instance" | "(" "Option" type ")" | "(" "Vec" type ")"
//!            | "(" "List" type ")" | "(" "Tuple" type* ")" | "(" "opaque" '"' ident '"' ")"
//! expr     ::= nat | ident | "(" "param" nat ")" | "(" "field" expr ident ")"
//!            | "(" "add" expr expr ")" | "(" "sub" expr expr ")" | "(" "mul" expr expr ")"
//!            | "(" "div" expr expr ")" | "(" "mod" expr expr ")" | "(" "shl" expr expr ")"
//!            | "(" "pow" expr expr ")" | "(" "opaque" '"' ident '"' ")"
//!            | "(" "eq" expr expr ")" | "(" "lt" expr expr ")" | "(" "le" expr expr ")"
//!            | "(" "gt" expr expr ")" | "(" "if" expr expr expr ")" | "(" "let" ident expr expr ")"
//!            | "(" "call" ident expr* ")"
//!            | "(" "cases" expr alt* default? ")"          ; LCNF cases_on
//!            | "(" "ctor" '"' ident '"' expr* ")"          ; constructor application
//!            | "(" "proj" '"' ident '"' nat expr ")"       ; structure projection
//!            | "(" "jp" ident "(" ident* ")" expr ")"      ; LCNF join point
//!            | "(" "jmp" ident expr* ")"                   ; LCNF jump
//!            | "(" "unreachable" ")"
//! alt      ::= "(" "alt" '"' ident '"' "(" ident* ")" expr ")"
//! default  ::= "(" "default" expr ")"
//! comment  ::= ";;" ... end-of-line                       ; skipped as whitespace
//! ```

use super::{Alt, Definition, Expr, Module, Type};
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

fn parse_type(input: &str) -> IResult<&str, Type> {
    ws(alt((
        value(Type::Nat, tag("Nat")),
        value(Type::Int, tag("Int")),
        value(Type::Bool, tag("Bool")),
        value(Type::Instance, tag("Instance")),
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
                    tuple((tag("field"), ws(parse_expr), ws(quoted_ident))),
                    |(_, e, f)| Expr::Field(Box::new(e), f),
                ),
                map(
                    tuple((tag("add"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Add(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("sub"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Sub(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("mul"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Mul(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("div"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Div(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("mod"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Mod(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("shl"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Shl(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("pow"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Pow(Box::new(a), Box::new(b)),
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
                    tuple((tag("proj"), ws(quoted_ident), ws(parse_u64), ws(parse_expr))),
                    |(_, ty, idx, e)| Expr::Proj(ty, idx, Box::new(e)),
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
            )),
        ))),
        ws(char(')')),
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
    let (rest, (_, name, definitions)) = ws(delimited(
        char('('),
        tuple((tag("module"), ws(ident), many0(ws(parse_definition)))),
        char(')'),
    ))(input)?;

    Ok((rest, Module { name, definitions }))
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let input = r#"(add (mul (param 0) (field (param 1) "o")) (param 2))"#;
        let (rest, expr) = parse_expr(input).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Add(_, _) => {}
            _ => panic!("Expected Add, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_class_index() {
        let input = r#"
(module UorAtlas.Kernel
  (def classIndex ((h2 Nat) (d Nat) (l Nat) (inst Instance)) Nat
    (add (mul (field inst "stride") h2)
         (add (mul (field inst "o") d) l)))
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
            (alt "Pair" (a b) (add a b))
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
        let (rest, expr) = parse_expr(r#"(proj "Pair" 0 (ctor "Pair" 1 2))"#).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Proj(ty, idx, e) => {
                assert_eq!(ty, "Pair");
                assert_eq!(idx, 0);
                assert!(matches!(*e, Expr::Ctor(..)));
            }
            _ => panic!("Expected Proj, got {:?}", expr),
        }
    }

    #[test]
    fn test_parse_jp_jmp() {
        let (rest, expr) =
            parse_expr(r#"(jp loop (i acc) (if (lt i 10) (jmp loop (add i 1) acc) acc))"#).unwrap();
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
    fn test_parse_gt() {
        let (rest, expr) = parse_expr("(gt (param 0) 1)").unwrap();
        assert!(rest.is_empty());
        assert!(matches!(expr, Expr::Gt(..)));
    }

    #[test]
    fn test_parse_pow() {
        let (rest, expr) = parse_expr("(pow 2 (sub (proj \"Instance\" 2 i) 1))").unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Pow(a, b) => {
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
}
