//! Closed aggregate bindings in promoted lists, including actual Foundry LCNF.
use prod_codegen::{
    generate_cargo_package, generate_core_wasm_package, generate_module, CargoPackageSpec,
    CoreWasmSpec, Error,
};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::{fs, path::PathBuf, process::Command};

const ACTUAL: &str = include_str!("fixtures/foundry_design_lcnf.ir");

#[test]
fn actual_foundry_design_catalogue_generates_from_unchanged_export() {
    // Exported with PrismPM 431cea8 from kernel-verified LexLean Presentation
    // source 82bd79c2822d98a2737f984928bd015cbcddaa8e995bd65a1f78d08665f2a1e3.
    // Original IR SHA256: a9f6dc5360041163b03d6024e3101c5bd7e65ddfb2231917ada555aa50f14771.
    assert_eq!(
        format!("{:x}", Sha256::digest(ACTUAL.as_bytes())),
        "a9f6dc5360041163b03d6024e3101c5bd7e65ddfb2231917ada555aa50f14771"
    );
    let (remaining, module) = parse_module(ACTUAL).unwrap();
    assert!(remaining.is_empty());
    let source = generate_module(&module).unwrap();
    assert!(source.contains("anonymousDesignCatalogue"));
}

#[test]
fn shared_aggregate_initializers_do_not_expand_exponentially_or_capture_user_names() {
    let mut types = String::from(r#"(type "Depth0" (ctor "Depth0.mk" (value Nat)))"#);
    let mut body = String::from(r#"(let value0 (ctor "Depth0.mk" 7) "#);
    for depth in 1..=12 {
        let previous = depth - 1;
        types.push_str(&format!(r#"(type "Depth{depth}" (ctor "Depth{depth}.mk" (left (named "Depth{previous}")) (right (named "Depth{previous}"))))"#));
        body.push_str(&format!(
            r#"(let value{depth} (ctor "Depth{depth}.mk" value{previous} value{previous}) "#
        ));
    }
    body.push_str(r#"(ctor "List.cons" value12 (ctor "List.nil"))"#);
    body.push_str(&")".repeat(13));
    let input=format!("(module Shared {types} (def __PROD_STATIC_CONSTANT_0 () Nat 3) (def shared () (List (named \"Depth12\")) {body}))");
    let (remaining, module) = parse_module(&input).unwrap();
    assert!(remaining.is_empty());
    let source = generate_module(&module).unwrap();
    assert!(
        source.len() < 16000,
        "shared constructor DAG expanded to {} source bytes",
        source.len()
    );
    assert_eq!(
        source.matches("    const __PROD_STATIC_CONSTANT_").count(),
        13
    );
    assert!(!source.contains("const __PROD_STATIC_CONSTANT_0:"));
    assert!(source.contains("const __PROD_STATIC_CONSTANT_1:"));
}

const TYPES: &str = r#"
  (type "Probe.Mode" (ctor "Probe.Mode.Light") (ctor "Probe.Mode.Dark"))
  (type "Probe.Token" (ctor "Probe.Token.mk" (value UInt8) (active Bool) (mode (named "Probe.Mode"))))
  (type "Probe.Pair" (ctor "Probe.Pair.mk" (left (named "Probe.Token")) (right (named "Probe.Token"))))
"#;

fn aggregate_ir() -> String {
    format!(
        r#"(module Aggregate {TYPES}
      (def values () (List (named "Probe.Pair"))
        (let n 255 (let yes true (let mode (ctor "Probe.Mode.Light")
          (let token (ctor "Probe.Token.mk" n yes mode)
            (let alias token (let n 1
              (let other (ctor "Probe.Token.mk" n false (ctor "Probe.Mode.Dark"))
                (let pair (ctor "Probe.Pair.mk" alias other)
                  (ctor "List.cons" pair (ctor "List.nil")))))))))))
      (def captured () (List (named "Probe.Token"))
        (let x (ctor "Probe.Token.mk" 3 true (ctor "Probe.Mode.Light"))
          (let xs (ctor "List.cons" x (ctor "List.nil"))
            (let x (ctor "Probe.Token.mk" 9 false (ctor "Probe.Mode.Dark"))
              (ctor "List.cons" x xs)))))
      (def empty_records () (List (named "Probe.Mode"))
        (let first (ctor "Probe.Mode.Light") (let second (ctor "Probe.Mode.Dark")
          (let alias first (ctor "List.cons" second (ctor "List.cons" alias (ctor "List.nil"))))))))"#
    )
}

#[test]
fn closed_aggregate_binding_accepts_nested_typed_fields_and_aliases() {
    let input = aggregate_ir();
    let (remaining, module) = parse_module(&input).unwrap();
    assert!(remaining.is_empty());
    let source = generate_module(&module).unwrap();
    assert!(source.contains("&'static [crate::Pair]"));
    assert!(!source.contains("alloc::"));
}

#[test]
fn aggregate_bindings_refuse_invalid_fields_computation_and_scope() {
    for body in [
        r#"(let x (ctor "Probe.Token.mk" 256 true (ctor "Probe.Mode.Light")) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Token.mk" 1 1 (ctor "Probe.Mode.Light")) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Token.mk" 1 true true) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Token.mk" 1 true) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Token.mk" 1 true (ctor "Probe.Unknown.mk")) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Token.mk" later true (ctor "Probe.Mode.Light")) (let later 1 (ctor "List.cons" x (ctor "List.nil"))))"#,
        r#"(let x (ctor "Probe.Token.mk" (sub 2 1) true (ctor "Probe.Mode.Light")) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Pair.mk" 1 2) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let xs (ctor "List.cons" x (ctor "List.nil")) (let x (ctor "Probe.Token.mk" 1 true (ctor "Probe.Mode.Light")) xs))"#,
        r#"(let x (ctor "Probe.Token.mk" x true (ctor "Probe.Mode.Light")) (ctor "List.cons" x (ctor "List.nil")))"#,
        r#"(let x (ctor "Probe.Token.mk" 1 true (ctor "Probe.Mode.Light")) (let alias x (let x 4 (ctor "List.cons" x (ctor "List.nil")))))"#,
    ] {
        let input = format!(
            "(module Invalid {TYPES} (def value () (List (named \"Probe.Token\")) {body}))"
        );
        let (remaining, module) = parse_module(&input).unwrap();
        assert!(remaining.is_empty());
        assert!(
            matches!(
                generate_module(&module),
                Err(Error::UnsupportedList(_))
                    | Err(Error::UnsupportedFieldType(_))
                    | Err(Error::UnresolvedCall(_))
            ),
            "{input}"
        );
    }
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "prod-static-aggregate-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained aggregate fixture: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
fn run(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

const RUNNER: &str = r#"use static_aggregate_fixture::*;
fn main() {
    let pair=&values()[0];
    assert_eq!((pair.left.value,pair.left.active),(255,true));
    assert_eq!((pair.right.value,pair.right.active),(1,false));
    assert_eq!(pair.left.mode,Mode::Light); assert_eq!(pair.right.mode,Mode::Dark);
    assert_eq!(captured().iter().map(|x|x.value).collect::<Vec<_>>(),[9,3]);
    assert_eq!(empty_records(),&[Mode::Dark,Mode::Light]);
    let pair=&anonymousDesignCatalogue()[0];
    assert_eq!(pair.light.surface,16777215);assert_eq!(pair.dark.surface,1120295);
    assert_eq!(pair.light.accent,1460642);assert_eq!(pair.dark.accent,10076159);
    assert_eq!(pair.light.fontFamily,FontFamily::System);assert_eq!(pair.dark.fontFamily,FontFamily::System);
    assert_eq!(pair.light.targetPixels,44);assert_eq!(pair.dark.targetPixels,44);
    assert!(core::ptr::eq(values().as_ptr(),values().as_ptr()));
    assert!(core::ptr::eq(anonymousDesignCatalogue().as_ptr(),anonymousDesignCatalogue().as_ptr()));
    assert_eq!(anonymousDesignBytes(vec![0]).unwrap(),[131,1,1,3]);
    let response=anonymousDesignBytes(vec![]).unwrap();
    println!("{}",response.iter().map(|b|format!("{b:02x}")).collect::<String>());
}"#;

const WASM_TEST: &str = r#"import assert from 'node:assert/strict';import {readFileSync} from 'node:fs';
function encode(v){if(Array.isArray(v))return Buffer.concat([head(4,v.length),...v.map(encode)]);if(typeof v==='string'){const b=Buffer.from(v);return Buffer.concat([head(3,b.length),b]);}return head(0,v);}
function head(major,v){if(v<24)return Buffer.from([(major<<5)+v]);const n=v<=255?1:v<=65535?2:4,b=Buffer.alloc(n+1);b[0]=(major<<5)+({1:24,2:25,4:26}[n]);b.writeUIntBE(v,1,n);return b;}
const tokens=colors=>[...colors,0,1000,1500,1000,500,72,18,48,44];
// DesignWire writes an unwrapped catalogue and seven uint24 color values.
const expected=encode([[tokens([0xffffff,0x17212f,0x526071,0x1649a2,0xffffff,0xa31616,0x6b21a8]),tokens([0x111827,0xf8fafc,0xa7b4c5,0x99bfff,0x111827,0xff9c9c,0xfcd34d])]]);
const module=new WebAssembly.Module(readFileSync(process.argv[2]));assert.deepEqual(WebAssembly.Module.imports(module),[]);
for(const [request,response]of [[Buffer.alloc(0),expected],[Buffer.from([0]),Buffer.from([131,1,1,3])]])for(let repeat=0;repeat<2;repeat++){
 const e=new WebAssembly.Instance(module,{}).exports,p=e.holo_alloc(request.length);new Uint8Array(e.memory.buffer,p,request.length).set(request);
 const result=BigInt.asUintN(64,e.holo_run(p,request.length)),at=Number(result>>32n),length=Number(result&0xffffffffn);
 assert.deepEqual(Buffer.from(new Uint8Array(e.memory.buffer,at,length)),response);
}
for(const path of process.argv.slice(3))assert.equal(readFileSync(path,'utf8').trim(),expected.toString('hex'));
"#;

#[test]
fn aggregate_constants_execute_native_no_std_and_actual_core_wasm() {
    let input = aggregate_ir();
    let (_, mut module) = parse_module(&input).unwrap();
    let (_, actual) = parse_module(ACTUAL).unwrap();
    module.types.extend(actual.types);
    module.definitions.extend(actual.definitions);
    let hash = format!(
        "{:x}",
        Sha256::digest([input.as_bytes(), ACTUAL.as_bytes()].concat())
    );
    let spec = CargoPackageSpec {
        name: "static-aggregate-fixture".into(),
        version: "0.1.0".into(),
        description: "Closed aggregate regression".into(),
        repository: "https://github.com/auser/lean4-prod".into(),
        homepage: "https://github.com/auser/lean4-prod".into(),
        readme: "Closed aggregate regression.\n".into(),
        license_mit: "MIT\n".into(),
        license_apache: "Apache-2.0\n".into(),
        input_sha256: hash.clone(),
        dependencies: vec![],
    };
    let package = generate_cargo_package(&module, &spec).unwrap();
    assert_eq!(package, generate_cargo_package(&module, &spec).unwrap());
    let scratch = Scratch::new();
    for file in package.files {
        let path = scratch.0.join("native").join(file.path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, file.bytes).unwrap();
    }
    fs::write(scratch.0.join("runner.rs"), RUNNER).unwrap();
    fs::write(scratch.0.join("wasm.mjs"), WASM_TEST).unwrap();
    let mut native_outputs = Vec::new();
    for standard in [false, true] {
        for optimized in [false, true] {
            let library = scratch
                .0
                .join(format!("libaggregate_{standard}_{optimized}.rlib"));
            let mut command = Command::new("rustc");
            command.args([
                "--edition=2021",
                "--crate-type=rlib",
                "--crate-name=static_aggregate_fixture",
            ]);
            if standard {
                command.args(["--cfg", "feature=\"std\""]);
            }
            if optimized {
                command.args(["-C", "opt-level=3", "-C", "overflow-checks=yes"]);
            }
            run(command
                .arg(scratch.0.join("native/src/lib.rs"))
                .arg("-o")
                .arg(&library));
            let runner = scratch.0.join(format!("runner_{standard}_{optimized}"));
            run(Command::new("rustc")
                .arg("--edition=2021")
                .arg(scratch.0.join("runner.rs"))
                .arg("--extern")
                .arg(format!("static_aggregate_fixture={}", library.display()))
                .arg("-o")
                .arg(&runner));
            let output = Command::new(runner).output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let path = scratch.0.join(format!("native_{standard}_{optimized}.hex"));
            fs::write(&path, output.stdout).unwrap();
            native_outputs.push(path);
        }
    }
    let package = generate_core_wasm_package(
        &module,
        &CoreWasmSpec {
            crate_name: "aggregate-guest".into(),
            entry: "anonymousDesignBytes".into(),
            export_name: "holo_run".into(),
            input_allocation_cap: 64,
            output_allocation_cap: 4096,
            maximum_pages: 32,
            input_ir_sha256: hash,
        },
    )
    .unwrap();
    let guest = scratch.0.join("guest");
    for file in package.files {
        let path = guest.join(file.path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, file.bytes).unwrap();
    }
    run(Command::new("cargo")
        .current_dir(&guest)
        .args(["build", "--locked", "--offline", "--release"])
        .env_remove("RUSTC_WRAPPER")
        .env("CARGO_TARGET_DIR", scratch.0.join("wasm-target")));
    run(Command::new("node")
        .arg(scratch.0.join("wasm.mjs"))
        .arg(
            scratch
                .0
                .join("wasm-target/wasm32-unknown-unknown/release/aggregate_guest.wasm"),
        )
        .args(native_outputs));
}
