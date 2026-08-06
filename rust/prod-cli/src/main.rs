//! prod-cli: Command-line tool for parsing Lean 4 IR and generating Rust
//!
//! Usage:
//!   prod parse module.ir
//!   prod gen module.ir [--output generated.rs]
//!   prod validate module.ir

mod roots;

use clap::{Parser, Subcommand};
use std::fs;

#[derive(Parser)]
#[command(name = "prod")]
#[command(about = "Lean 4 → prod IR parser and Rust code generator")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse an IR file and print its AST
    Parse {
        /// Path to the IR file
        path: String,
    },
    /// Generate Rust code from an IR file (prints to stdout unless --output is given)
    Gen {
        /// Path to the IR file
        path: String,
        /// Output path for generated Rust code
        #[arg(short, long)]
        output: Option<String>,
    },
    /// Validate an IR file (check for unsupported constructs)
    Validate {
        /// Path to the IR file
        path: String,
    },
    /// Analyze proof roots exported by Lean.
    Roots {
        #[command(subcommand)]
        command: RootCommands,
    },
}

#[derive(Subcommand)]
enum RootCommands {
    /// Check dependency acyclicity and root dependency coverage.
    Check {
        path: String,
        /// Include auto-generated roots (default: hand-written roots only)
        #[arg(long)]
        all: bool,
    },
    /// Print roots on the Pareto front of proof size and kernel depth.
    Pareto {
        path: String,
        /// Include auto-generated roots (default: hand-written roots only)
        #[arg(long)]
        all: bool,
    },
    /// Generate bridges between roots sharing kernel dependencies.
    Connect {
        path: String,
        root1: Option<String>,
        root2: Option<String>,
        /// Include auto-generated roots (default: hand-written roots only)
        #[arg(long)]
        all: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Parse { path } => {
            let content = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e));
            let (_, module) = prod_ir::parser::parse_module(&content)
                .unwrap_or_else(|e| panic!("Parse error: {:?}", e));
            println!("Module: {}", module.name);
            for def in &module.definitions {
                println!("  Def: {} -> {:?}", def.name, def.ret);
                println!("    Params: {:?}", def.params);
                println!("    Body: {:?}", def.body);
            }
        }
        Commands::Gen { path, output } => {
            let content = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e));
            let (_, module) = prod_ir::parser::parse_module(&content)
                .unwrap_or_else(|e| panic!("Parse error: {:?}", e));

            let body = prod_codegen::generate_module(&module)
                .unwrap_or_else(|e| panic!("Codegen error: {}", e));

            let mut out = String::from("#![allow(dead_code)]\n\n");
            out.push_str(&format!("// Generated from Lean 4 module: {}\n\n", module.name));
            out.push_str(&body);

            match output {
                Some(output) => {
                    fs::write(&output, out)
                        .unwrap_or_else(|e| panic!("Failed to write {}: {}", output, e));
                    println!("Generated: {}", output);
                }
                None => print!("{}", out),
            }
        }
        Commands::Validate { path } => {
            let content = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e));
            match prod_ir::parser::parse_module(&content) {
                Ok((_, module)) => {
                    println!("✓ Valid IR: {} definitions in module '{}'",
                        module.definitions.len(), module.name);
                    let opaque: Vec<_> = module.definitions.iter()
                        .filter(|d| matches!(d.body, prod_ir::Expr::Opaque(_)))
                        .collect();
                    if !opaque.is_empty() {
                        println!("⚠ {} definitions contain opaque expressions", opaque.len());
                    }
                }
                Err(e) => {
                    eprintln!("✗ Invalid IR: {:?}", e);
                    std::process::exit(1);
                }
            }
        }
        Commands::Roots { command } => match command {
            RootCommands::Check { path, all } => {
                let roots = roots::load(&path).unwrap_or_else(|e| panic!("{e}"));
                let roots = roots::filter_roots(roots, all);
                let report = roots::check(&roots);
                println!(
                    "Loaded {} roots{}.",
                    roots.len(),
                    if all { " (including auto-generated)" } else { "" }
                );
                println!(
                    "Checking dependency acyclicity... {}",
                    if report.acyclic { "OK" } else { "FAILED" }
                );
                println!(
                    "Roots with empty dependencies: {}",
                    report.empty_dependencies.len()
                );
                if !report.duplicate_ids.is_empty() {
                    println!(
                        "Warning: duplicate root ids: {}",
                        report.duplicate_ids.join(", ")
                    );
                }
                if report.acyclic && report.empty_dependencies.is_empty() {
                    println!("All root checks passed.");
                } else {
                    std::process::exit(1);
                }
            }
            RootCommands::Pareto { path, all } => {
                let roots = roots::load(&path).unwrap_or_else(|e| panic!("{e}"));
                let roots = roots::filter_roots(roots, all);
                let front = roots::pareto_front(&roots);
                println!("Pareto front: {} roots", front.len());
                for idx in front {
                    let root = &roots[idx];
                    println!(
                        "  {} [{}] (proof_term_size={}, kernel_depth={})",
                        roots::short_name(&root.id),
                        root.id,
                        root.proof_term_size,
                        root.kernel_depth
                    );
                }
            }
            RootCommands::Connect {
                path,
                root1,
                root2,
                all,
            } => {
                let roots = roots::load(&path).unwrap_or_else(|e| panic!("{e}"));
                let roots = roots::filter_roots(roots, all);
                let candidates = roots::bridges(&roots);
                let selected = match (root1, root2) {
                    (Some(a), Some(b)) => candidates
                        .into_iter()
                        .filter(|bridge| {
                            (roots::id_matches(&roots[bridge.left].id, &a)
                                && roots::id_matches(&roots[bridge.right].id, &b))
                                || (roots::id_matches(&roots[bridge.left].id, &b)
                                    && roots::id_matches(&roots[bridge.right].id, &a))
                        })
                        .collect(),
                    (None, None) => candidates,
                    _ => {
                        eprintln!("connect expects either zero or two root ids");
                        std::process::exit(2);
                    }
                };
                for bridge in &selected {
                    let left = roots::short_name(&roots[bridge.left].id);
                    let right = roots::short_name(&roots[bridge.right].id);
                    println!("bridge_{left}_{right}: {left} ↔ {right}");
                    println!("  shared kernel dependencies: {}", bridge.shared.join(", "));
                }
                println!("Generated {} bridge hypotheses.", selected.len());
            }
        },
    }
}
