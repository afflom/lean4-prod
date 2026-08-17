//! One place that guarantees distinct Lean names stay distinct.
//!
//! Lean names are namespaced (`UorAtlas.Instance`); most targets are not.
//! Rust drops the namespace and keeps only the last component, escaping a
//! keyword collision with `r#` -- reversible, so two distinct Lean names can
//! never land on one Rust identifier *by construction* of the escape itself.
//! Python cannot escape a keyword; it must rename (`type` -> `type_`), and a
//! rename is exactly where two distinct inputs can silently become one: a
//! sibling literally named `type_` collides with the renamed `type` and nothing
//! about the renaming itself would notice. C has no namespaces at all, so
//! every name -- type, constructor, field, definition -- flattens into one
//! global symbol space.
//!
//! `NameTable::build` is the one place that checks this, for every policy:
//! it mangles each Lean name into a target name and refuses to publish a
//! `NameTable` where two distinct Lean names produced the same target name,
//! naming both sources in the rejection. Without that check this module is
//! just a mangler; with it, a whole class of silent miscompilation becomes a
//! named rejection instead.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use prod_ir::Module;

/// Rust keywords that a Lean name may legitimately be. Shared by every
/// backend that wants Rust's own keyword list (today, only `prod-codegen`).
pub const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub",
    "ref", "return", "self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use",
    "where", "while", "abstract", "become", "box", "do", "final", "macro", "override", "priv",
    "typeof", "unsized", "virtual", "yield", "try", "gen",
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EscapeStrategy {
    /// Rust: `r#type`. Reversible.
    RawIdentifier,
    /// Python, C: `type_`. NOT reversible, which is why injectivity is checked.
    SuffixUnderscore,
}

pub struct NamePolicy {
    pub keywords: &'static [&'static str],
    pub escape: EscapeStrategy,
    /// C has no namespaces: `A.B.c` must become one globally unique symbol.
    pub flatten_namespaces: bool,
}

impl NamePolicy {
    pub const RUST: NamePolicy = NamePolicy {
        keywords: RUST_KEYWORDS,
        escape: EscapeStrategy::RawIdentifier,
        flatten_namespaces: false,
    };
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameError {
    Collision {
        target: String,
        first: String,
        second: String,
    },
}

#[derive(Debug)]
pub struct NameTable {
    forward: BTreeMap<String, String>,
}

impl NameTable {
    pub fn target_name(&self, lean_name: &str) -> Option<&str> {
        self.forward.get(lean_name).map(|s| s.as_str())
    }

    /// Walk every type, constructor, field and definition name in `module`,
    /// mangle each under `policy`, and build the forward Lean-name ->
    /// target-name map -- rejecting on the first pair of distinct Lean names
    /// that land on the same target name within a scope that would actually
    /// collide in the generated output.
    ///
    /// "Within a scope that would actually collide" matters: Rust has real
    /// namespaces below the module level even without `flatten_namespaces`.
    /// A type's constructors become that type's own enum variants (or its
    /// one struct), so two constructors of *different* types cannot collide
    /// -- practically every single-constructor Lean structure names its
    /// constructor `mk`, so treating every constructor name as one global
    /// pool would reject nearly any multi-type module. The same is true one
    /// level down for a constructor's own fields (struct fields are scoped
    /// to their struct/variant), and types live in a namespace separate from
    /// top-level definitions (Rust's own type vs. value namespaces mean a
    /// struct and a function of the same name do not collide). When
    /// `policy.flatten_namespaces` is set (C's case), every one of those
    /// scopes collapses into a single global one, matching the target having
    /// no namespaces of its own.
    pub fn build(module: &Module, policy: &NamePolicy) -> Result<NameTable, NameError> {
        let mut forward: BTreeMap<String, String> = BTreeMap::new();
        let mut global_scope: BTreeMap<String, String> = BTreeMap::new();
        let mut type_scope: BTreeMap<String, String> = BTreeMap::new();
        let mut def_scope: BTreeMap<String, String> = BTreeMap::new();

        for ty in &module.types {
            let target = mangle(&ty.name, policy);
            let scope = if policy.flatten_namespaces {
                &mut global_scope
            } else {
                &mut type_scope
            };
            insert_checked(scope, &target, &ty.name)?;
            forward.insert(ty.name.clone(), target);

            let mut ctor_scope: BTreeMap<String, String> = BTreeMap::new();
            for ctor in &ty.ctors {
                let ctor_target = mangle(&ctor.name, policy);
                let scope = if policy.flatten_namespaces {
                    &mut global_scope
                } else {
                    &mut ctor_scope
                };
                insert_checked(scope, &ctor_target, &ctor.name)?;
                forward.insert(ctor.name.clone(), ctor_target);

                let mut field_scope: BTreeMap<String, String> = BTreeMap::new();
                for (field_name, _field_ty) in &ctor.fields {
                    let field_target = mangle(field_name, policy);
                    let scope = if policy.flatten_namespaces {
                        &mut global_scope
                    } else {
                        &mut field_scope
                    };
                    insert_checked(scope, &field_target, field_name)?;
                    forward.insert(field_name.clone(), field_target);
                }
            }
        }

        for def in &module.definitions {
            let target = mangle(&def.name, policy);
            let scope = if policy.flatten_namespaces {
                &mut global_scope
            } else {
                &mut def_scope
            };
            insert_checked(scope, &target, &def.name)?;
            forward.insert(def.name.clone(), target);
        }

        Ok(NameTable { forward })
    }
}

/// Insert `source`'s mangled `target` into a collision-detection scope.
/// Rejects only when `target` is already claimed by a *different* Lean
/// source -- the same source reappearing under the same target (e.g. a
/// declaration seen twice) is not a collision.
fn insert_checked(
    scope: &mut BTreeMap<String, String>,
    target: &str,
    source: &str,
) -> Result<(), NameError> {
    if let Some(previous) = scope.get(target) {
        if previous != source {
            return Err(NameError::Collision {
                target: String::from(target),
                first: previous.clone(),
                second: String::from(source),
            });
        }
        return Ok(());
    }
    scope.insert(String::from(target), String::from(source));
    Ok(())
}

/// Last dot-separated component of a full Lean name.
fn last_component(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// A full Lean name as a target identifier: the last component (or the
/// whole name, flattened, under `flatten_namespaces`), escaped if it is one
/// of the policy's keywords.
fn mangle(name: &str, policy: &NamePolicy) -> String {
    let component = if policy.flatten_namespaces {
        name.replace('.', "_")
    } else {
        String::from(last_component(name))
    };
    if policy.keywords.contains(&component.as_str()) {
        match policy.escape {
            EscapeStrategy::RawIdentifier => format!("r#{}", component),
            EscapeStrategy::SuffixUnderscore => format!("{}_", component),
        }
    } else {
        component
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use prod_ir::{CtorDecl, Module, TypeDecl};

    fn module_with_types(names: &[&str]) -> Module {
        Module {
            name: String::from("M"),
            types: names
                .iter()
                .map(|n| TypeDecl {
                    name: String::from(*n),
                    ctors: vec![CtorDecl {
                        name: format!("{}.mk", n),
                        fields: vec![],
                    }],
                    unsupported: None,
                    invariant: None,
                })
                .collect(),
            definitions: vec![],
        }
    }

    #[test]
    fn distinct_lean_names_that_flatten_to_one_target_name_are_rejected() {
        // The failure this component exists to prevent. Both flatten to
        // `Instance`; `crate::Instance` can only mean one of them, and
        // whichever loses is silently miscompiled.
        let m = module_with_types(&["A.Instance", "B.Instance"]);
        let err = NameTable::build(&m, &NamePolicy::RUST).unwrap_err();
        assert!(
            matches!(&err, NameError::Collision { target, .. } if target == "Instance"),
            "expected a collision on `Instance`, got {:?}",
            err
        );
    }

    #[test]
    fn distinct_names_that_stay_distinct_are_accepted() {
        let m = module_with_types(&["A.Instance", "A.Window"]);
        let table = NameTable::build(&m, &NamePolicy::RUST).expect("no collision");
        assert_eq!(table.target_name("A.Instance"), Some("Instance"));
        assert_eq!(table.target_name("A.Window"), Some("Window"));
    }

    #[test]
    fn a_keyword_name_is_escaped_not_renamed_under_the_rust_policy() {
        let m = module_with_types(&["A.type"]);
        let table = NameTable::build(&m, &NamePolicy::RUST).expect("no collision");
        assert_eq!(table.target_name("A.type"), Some("r#type"));
    }

    #[test]
    fn a_rename_policy_still_produces_injective_names() {
        // Python cannot escape, so it renames -- and renaming is exactly where
        // two distinct inputs silently become one. `type` renames to `type_`,
        // so a sibling literally named `type_` must collide rather than be
        // silently merged.
        let policy = NamePolicy {
            keywords: &["type"],
            escape: EscapeStrategy::SuffixUnderscore,
            flatten_namespaces: false,
        };
        let m = module_with_types(&["A.type", "A.type_"]);
        let err = NameTable::build(&m, &policy).unwrap_err();
        assert!(matches!(&err, NameError::Collision { target, .. } if target == "type_"));
    }
}
