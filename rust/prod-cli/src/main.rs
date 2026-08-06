//! prod-cli: Command-line tool for parsing Lean 4 IR and generating Rust
//!
//! Usage:
//!   prod parse module.ir
//!   prod gen module.ir [--output generated.rs]
//!   prod validate module.ir

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
    }
}
