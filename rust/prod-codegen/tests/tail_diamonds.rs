//! Join-diamond fallback: lexical identity, eager errors, owned/borrowed values.
use prod_codegen::{
    generate_cargo_package, generate_core_wasm_package, generate_module, CargoPackageSpec,
    CoreWasmSpec,
};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::{fs, path::PathBuf, process::Command};

fn diamond(name: &str, input: &str, result: &str, finish: &str, scalar: bool) -> String {
    let mut body = format!("(let captured 7 (let join0 (jp join0 (arg0) {finish}) ");
    for i in 1..=16 {
        let previous = i - 1;
        let yes = if scalar {
            format!("(let captured 1 (jmp join{previous} (add arg{i} captured)))")
        } else {
            format!("(jmp join{previous} arg{i})")
        };
        let no = if scalar {
            format!("(let captured 2 (jmp join{previous} (add arg{i} captured)))")
        } else {
            format!("(jmp join{previous} arg{i})")
        };
        body.push_str(&format!(
            "(let join{i} (jp join{i} (arg{i}) (if flag {yes} {no})) "
        ));
    }
    body.push_str("(let captured 999 (jmp join16 input))");
    body.push_str(&")".repeat(18));
    format!("(def {name} ((flag Bool) (input {input})) {result} {body})")
}

fn input() -> String {
    let scalar = diamond("selected", "Nat", "Nat", "(add arg0 captured)", true);
    let shadow=diamond("shadowed","Nat","Nat","(let same (jp same (value) (add value captured)) (let first (jmp same arg0) (let same (jp same (value) (add value 100)) (add first (jmp same arg0)))))",true);
    let owned = diamond("owned", "(named \"Row\")", "(named \"Row\")", "arg0", false);
    let borrowed = diamond(
        "borrowed",
        "(named \"Row\")",
        "Nat",
        "(length (proj \"Row\" \"bytes\" arg0))",
        false,
    );
    let copied = diamond(
        "copied",
        "(named \"CopyRow\")",
        "(named \"CopyRow\")",
        "arg0",
        false,
    );
    let list = diamond("borrowed_list", "(List Nat)", "Nat", "(length arg0)", false);
    let error = diamond(
        "selected_error",
        "Nat",
        "Nat",
        "(if flag arg0 (add 18446744073709551615 1))",
        false,
    );
    let local_rows = |definition: String| {
        let pattern = "(if flag (jmp join0 arg1) (jmp join0 arg1))";
        assert_eq!(definition.matches(pattern).count(), 1);
        definition.replacen(pattern,"(if flag (let local (ctor \"Row.mk\" (bytes 1 2)) (jmp join0 local)) (let local (ctor \"Row.mk\" (bytes 3 4 5)) (jmp join0 local)))",1)
    };
    let local_owned = local_rows(diamond(
        "local_owned",
        "(named \"Row\")",
        "(named \"Row\")",
        "arg0",
        false,
    ));
    let local_borrowed = local_rows(diamond(
        "local_borrowed",
        "(named \"Row\")",
        "Nat",
        "(length (proj \"Row\" \"bytes\" arg0))",
        false,
    ));
    format!("(module TailDiamonds (type \"Row\" (ctor \"Row.mk\" (bytes Bytes))) (type \"CopyRow\" (ctor \"CopyRow.mk\" (value Nat))) {scalar} {shadow} {owned} {borrowed} {copied} {list} {error} {local_owned} {local_borrowed} (def run ((request Bytes)) Bytes (let answer (call selected (eq (length request) 1) 10) (if (eq answer 33) (bytes 1) (bytes 2)))))")
}

#[test]
fn actual_unmodified_foundry_export_generates_without_expansion_explosion() {
    let actual = include_str!("fixtures/foundry_anonymous_ui_lcnf.ir");
    let (rest, module) = parse_module(actual).unwrap();
    assert!(rest.is_empty());
    let source = generate_module(&module).unwrap();
    assert!(
        source.len() < 1_000_000,
        "source expansion: {} bytes",
        source.len()
    );
    assert!(source.contains("anonymousPresentation"));
}

#[test]
fn malformed_branch_argument_types_cannot_become_an_executable() {
    // Join parameters are untyped in prod-ir. Factoring makes no new claim of
    // complete IR type-checking; unchanged Rust type constraints must refuse
    // a raw input whose Bool argument is consumed as Nat.
    let definition = diamond("invalid", "Nat", "Nat", "arg0", false).replacen(
        "(jmp join0 arg1)",
        "(jmp join0 true)",
        1,
    );
    let input = format!("(module Invalid {definition})");
    let (rest, module) = parse_module(&input).unwrap();
    assert!(rest.is_empty());
    let source = generate_module(&module).unwrap();
    let scratch = Scratch::new();
    let path = scratch.0.join("invalid.rs");
    fs::write(&path, source).unwrap();
    let output = Command::new("rustc")
        .args(["--edition=2021", "--crate-type=lib"])
        .arg(&path)
        .arg("-o")
        .arg(scratch.0.join("invalid.rlib"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("error[E0308]"));
    assert!(!scratch.0.join("invalid.rlib").exists());
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let n = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let p = std::env::temp_dir().join(format!("prod-tail-diamonds-{}-{n}", std::process::id()));
        fs::create_dir(&p).unwrap();
        Self(p)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained tail-diamond fixture: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
fn run(command: &mut Command) -> String {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn factored_joins_execute_with_scope_ownership_and_checked_errors() {
    let input = input();
    let (rest, module) = parse_module(&input).unwrap();
    assert!(rest.is_empty());
    let source = generate_module(&module).unwrap();
    assert!(source.len() < 100_000);
    let hash = format!("{:x}", Sha256::digest(input.as_bytes()));
    let scratch = Scratch::new();
    let package = generate_cargo_package(
        &module,
        &CargoPackageSpec {
            name: "tail-diamonds-fixture".into(),
            version: "0.1.0".into(),
            description: "Tail continuation regression".into(),
            repository: "https://example.invalid/fixture".into(),
            homepage: "https://example.invalid/fixture".into(),
            readme: "Fixture\n".into(),
            license_mit: "MIT\n".into(),
            license_apache: "Apache-2.0\n".into(),
            input_sha256: hash.clone(),
            dependencies: vec![],
        },
    )
    .unwrap();
    for file in package.files {
        let path = scratch.0.join(&file.path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, file.bytes).unwrap();
    }
    fs::create_dir(scratch.0.join("examples")).unwrap();
    fs::write(
        scratch.0.join("examples/probe.rs"),
        r#"use tail_diamonds_fixture::*;
fn main() {
    for flag in [false,true] {
        let n=if flag{16}else{32};
        assert_eq!(selected(flag,10).unwrap(),17+n);
        assert_eq!(shadowed(flag,10).unwrap(),2*(10+n)+107);
        let bytes=vec![0,1,255];
        let row=Row{bytes:bytes.clone()};
        assert_eq!(owned(flag,&row).bytes,bytes);
        assert_eq!(borrowed(flag,&row),3);
        let local=if flag{vec![1,2]}else{vec![3,4,5]};
        assert_eq!(local_owned(flag,&row).bytes,local);
        assert_eq!(local_borrowed(flag,&row),local.len() as u64);
        assert_eq!(copied(flag,CopyRow{value:99}).value,99);
        assert_eq!(borrowed_list(flag,&[1,2,3]),3);
        assert!(selected(flag,u64::MAX).is_err());
    }
    assert_eq!(selected_error(true,7).unwrap(),7);
    assert!(selected_error(false,7).is_err());
    assert_eq!(run(vec![0]).unwrap(),[1]);assert_eq!(run(vec![]).unwrap(),[2]);
    println!("PASS scope, owned, borrowed, copied, list, eager errors");
}"#,
    )
    .unwrap();
    for standard in [true, false] {
        for optimized in [true, false] {
            let mut command = Command::new("cargo");
            command.current_dir(&scratch.0).args([
                "run",
                "--locked",
                "--offline",
                "--example",
                "probe",
            ]);
            if !standard {
                command.arg("--no-default-features");
            }
            if optimized {
                command.arg("--release");
            }
            command.env(
                "CARGO_TARGET_DIR",
                scratch.0.join(format!("target-{standard}-{optimized}")),
            );
            assert!(run(&mut command)
                .contains("PASS scope, owned, borrowed, copied, list, eager errors"));
        }
    }
    let guest = scratch.0.join("guest");
    fs::create_dir(&guest).unwrap();
    let package = generate_core_wasm_package(
        &module,
        &CoreWasmSpec {
            crate_name: "tail-diamonds-guest".into(),
            entry: "run".into(),
            export_name: "holo_run".into(),
            input_allocation_cap: 1024,
            output_allocation_cap: 1024,
            maximum_pages: 16,
            input_ir_sha256: hash,
        },
    )
    .unwrap();
    for file in package.files {
        let path = guest.join(&file.path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, file.bytes).unwrap();
    }
    run(Command::new("cargo")
        .current_dir(&guest)
        .args(["build", "--locked", "--offline", "--release"])
        .env("CARGO_TARGET_DIR", scratch.0.join("wasm-target")));
    fs::write(scratch.0.join("wasm.mjs"),r#"import assert from 'node:assert/strict';import{readFileSync}from'node:fs';const m=new WebAssembly.Module(readFileSync(process.argv[2]));assert.deepEqual(WebAssembly.Module.imports(m),[]);for(const [input,expected]of[[[],2],[[0],1],[[0,1],2]])for(let repeat=0;repeat<2;repeat++){const i=new WebAssembly.Instance(m,{}),p=i.exports.holo_alloc(input.length);new Uint8Array(i.exports.memory.buffer,p,input.length).set(input);const result=BigInt.asUintN(64,i.exports.holo_run(p,input.length)),at=Number(result>>32n),len=Number(result&0xffffffffn);assert.equal(len,1);assert.equal(new Uint8Array(i.exports.memory.buffer,at,len)[0],expected);}console.log('PASS genuine factored Core-Wasm');"#).unwrap();
    assert!(
        run(Command::new("node").arg(scratch.0.join("wasm.mjs")).arg(
            scratch
                .0
                .join("wasm-target/wasm32-unknown-unknown/release/tail_diamonds_guest.wasm")
        ))
        .contains("PASS genuine factored Core-Wasm")
    );
}
