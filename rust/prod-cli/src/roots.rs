//! Proof-root graph analysis over the Lean-exported `roots.json` format.

use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct Root {
    /// Full Lean name — unique by kernel construction, so it is the identity.
    pub id: String,
    /// `true` for Lean-generated machinery (equation lemmas, omega
    /// certificates, structure projections). Missing in older `roots.json`
    /// files; serde's default treats it as `false` (backward compatible:
    /// unknown roots stay visible rather than being silently dropped).
    #[serde(default)]
    pub auto: bool,
    pub dependencies: Vec<String>,
    pub proof_term_size: u64,
    pub kernel_depth: u64,
    /// Wall time (ns) for re-typechecking the proof term with Lean's kernel,
    /// measured by the exporter (`Lean.Kernel.check`). Machine-dependent;
    /// used as the third, relative Pareto objective. Missing in older
    /// `roots.json` files; serde's default treats it as `0` (when uniformly
    /// absent, dominance reduces to the old two-objective rule).
    #[serde(default)]
    pub check_time_ns: u64,
}

#[derive(Debug, Deserialize)]
struct RootFile {
    roots: Vec<Root>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bridge {
    pub left: usize,
    pub right: usize,
    pub shared: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckReport {
    pub acyclic: bool,
    pub duplicate_ids: Vec<String>,
    pub empty_dependencies: Vec<usize>,
}

pub fn load(path: impl AsRef<Path>) -> Result<Vec<Root>, String> {
    let path = path.as_ref();
    let contents = fs::read_to_string(path)
        .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
    serde_json::from_str::<RootFile>(&contents)
        .map(|file| file.roots)
        .map_err(|e| format!("failed to parse {}: {e}", path.display()))
}

/// Short display name: last dot-separated component of the full id.
/// Identity/uniqueness always comes from the full id; this is display-only.
pub fn short_name(id: &str) -> &str {
    id.rsplit('.').next().unwrap_or(id)
}

/// Drop auto-generated roots unless `include_auto` is set. `roots check`,
/// `pareto`, and `connect` default to hand-written roots only.
pub fn filter_roots(roots: Vec<Root>, include_auto: bool) -> Vec<Root> {
    if include_auto {
        roots
    } else {
        roots.into_iter().filter(|root| !root.auto).collect()
    }
}

/// Match a CLI-supplied name against a root: full id, or short name as a
/// convenience. Identity stays with the full id.
pub fn id_matches(id: &str, query: &str) -> bool {
    id == query || short_name(id) == query
}

/// Match both the compact root id and Lean's fully-qualified dependency name.
fn dependency_matches_id(dependency: &str, id: &str) -> bool {
    dependency == id || dependency.rsplit('.').next() == Some(id)
}

fn adjacency(roots: &[Root]) -> Vec<Vec<usize>> {
    roots
        .iter()
        .map(|root| {
            root.dependencies
                .iter()
                .flat_map(|dependency| {
                    roots.iter().enumerate().filter_map(|(idx, candidate)| {
                        dependency_matches_id(dependency, &candidate.id).then_some(idx)
                    })
                })
                .collect()
        })
        .collect()
}

fn is_acyclic_from(graph: &[Vec<usize>], node: usize, states: &mut [u8]) -> bool {
    match states[node] {
        1 => return false,
        2 => return true,
        _ => {}
    }
    states[node] = 1;
    if graph[node]
        .iter()
        .any(|&next| !is_acyclic_from(graph, next, states))
    {
        return false;
    }
    states[node] = 2;
    true
}

pub fn check(roots: &[Root]) -> CheckReport {
    let mut ids: BTreeMap<&str, usize> = BTreeMap::new();
    let mut duplicate_ids = BTreeSet::new();
    for root in roots {
        let count = ids.entry(&root.id).or_default();
        *count += 1;
        if *count > 1 {
            duplicate_ids.insert(root.id.clone());
        }
    }
    let duplicate_ids = duplicate_ids.into_iter().collect();
    let empty_dependencies = roots
        .iter()
        .enumerate()
        .filter_map(|(idx, root)| root.dependencies.is_empty().then_some(idx))
        .collect();
    let graph = adjacency(roots);
    let mut states = vec![0; roots.len()];
    let acyclic = (0..roots.len()).all(|node| is_acyclic_from(&graph, node, &mut states));
    CheckReport {
        acyclic,
        duplicate_ids,
        empty_dependencies,
    }
}

pub fn dominates(a: &Root, b: &Root) -> bool {
    a.proof_term_size <= b.proof_term_size
        && a.kernel_depth <= b.kernel_depth
        && a.check_time_ns <= b.check_time_ns
        && (a.proof_term_size < b.proof_term_size
            || a.kernel_depth < b.kernel_depth
            || a.check_time_ns < b.check_time_ns)
}

pub fn pareto_front(roots: &[Root]) -> Vec<usize> {
    roots
        .iter()
        .enumerate()
        .filter(|(idx, candidate)| {
            !roots
                .iter()
                .enumerate()
                .any(|(other_idx, other)| other_idx != *idx && dominates(other, candidate))
        })
        .map(|(idx, _)| idx)
        .collect()
}

pub fn bridges(roots: &[Root]) -> Vec<Bridge> {
    let mut result = Vec::new();
    for left in 0..roots.len() {
        for right in (left + 1)..roots.len() {
            let a = &roots[left];
            let b = &roots[right];
            let directly_connected = a
                .dependencies
                .iter()
                .any(|dep| dependency_matches_id(dep, &b.id))
                || b.dependencies
                    .iter()
                    .any(|dep| dependency_matches_id(dep, &a.id));
            if directly_connected {
                continue;
            }
            let b_deps: BTreeSet<&str> = b.dependencies.iter().map(String::as_str).collect();
            let shared = a
                .dependencies
                .iter()
                .filter(|dep| b_deps.contains(dep.as_str()))
                .cloned()
                .collect::<Vec<_>>();
            if !shared.is_empty() {
                result.push(Bridge { left, right, shared });
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root(id: &str, deps: &[&str], size: u64, depth: u64, check_time_ns: u64) -> Root {
        Root {
            id: id.into(),
            auto: false,
            dependencies: deps.iter().map(|dep| (*dep).into()).collect(),
            proof_term_size: size,
            kernel_depth: depth,
            check_time_ns,
        }
    }

    fn auto_root(id: &str, deps: &[&str], size: u64, depth: u64, check_time_ns: u64) -> Root {
        Root {
            auto: true,
            ..root(id, deps, size, depth, check_time_ns)
        }
    }

    #[test]
    fn check_detects_cycles_and_duplicate_ids() {
        let roots = vec![
            root("a", &["b"], 1, 1, 10),
            root("b", &["a"], 2, 2, 20),
            root("a", &[], 3, 3, 30),
        ];
        let report = check(&roots);
        assert!(!report.acyclic);
        assert_eq!(report.duplicate_ids, vec!["a"]);
        assert_eq!(report.empty_dependencies, vec![2]);
    }

    #[test]
    fn pareto_front_filters_dominated_roots() {
        let roots = vec![
            root("small", &[], 2, 2, 100),
            root("deep", &[], 1, 4, 50),
            root("dominated", &[], 3, 3, 300),
            // Same size/depth as `small`, but slower to re-check: dominated
            // only through the third (check-time) objective.
            root("slow_check", &[], 2, 2, 150),
        ];
        assert_eq!(pareto_front(&roots), vec![0, 1]);
        assert!(dominates(&roots[0], &roots[2]));
        assert!(dominates(&roots[0], &roots[3]));
        assert!(!dominates(&roots[3], &roots[0]));
    }

    #[test]
    fn bridges_use_shared_dependencies_and_skip_direct_edges() {
        let roots = vec![
            root("a", &["shared"], 1, 1, 10),
            root("b", &["shared"], 2, 2, 20),
            root("c", &["a", "b", "shared"], 3, 3, 30),
        ];
        assert_eq!(
            bridges(&roots),
            vec![Bridge {
                left: 0,
                right: 1,
                shared: vec!["shared".into()],
            }]
        );
    }

    #[test]
    fn missing_auto_field_defaults_to_false() {
        // Backward compatibility: old roots.json files have no `auto` and no
        // `check_time_ns` field.
        let json = r#"{"roots":[
            {"id":"UorAtlas.foo","dependencies":[],"proof_term_size":1,"kernel_depth":1},
            {"id":"UorAtlas.foo.eq_1","auto":true,"dependencies":[],"proof_term_size":2,"kernel_depth":2,"check_time_ns":42}
        ]}"#;
        let roots = serde_json::from_str::<RootFile>(json).unwrap().roots;
        assert!(!roots[0].auto);
        assert_eq!(roots[0].check_time_ns, 0);
        assert!(roots[1].auto);
        assert_eq!(roots[1].check_time_ns, 42);
    }

    #[test]
    fn filter_roots_drops_auto_roots_unless_included() {
        let roots = vec![
            root("UorAtlas.real", &[], 1, 1, 10),
            auto_root("UorAtlas.f.eq_1", &[], 2, 2, 20),
        ];
        let filtered = filter_roots(roots.clone(), false);
        assert_eq!(filtered, vec![roots[0].clone()]);
        assert_eq!(filter_roots(roots.clone(), true), roots);
    }

    #[test]
    fn full_name_ids_are_unique_when_short_names_collide() {
        let roots = vec![
            root("UorAtlas.f.eq_1", &[], 1, 1, 10),
            root("UorAtlas.g.eq_1", &[], 1, 1, 10),
        ];
        assert!(check(&roots).duplicate_ids.is_empty());
        assert_eq!(short_name(&roots[0].id), short_name(&roots[1].id));
    }

    #[test]
    fn id_matches_accepts_full_id_or_short_name() {
        assert!(id_matches(
            "_private.M.0.UorAtlas.digits_lt_stride",
            "_private.M.0.UorAtlas.digits_lt_stride"
        ));
        assert!(id_matches(
            "_private.M.0.UorAtlas.digits_lt_stride",
            "digits_lt_stride"
        ));
        assert!(!id_matches("UorAtlas.classIndex", "digits_lt_stride"));
    }
}
