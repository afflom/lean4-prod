//! Malformed static aggregate input is a recoverable compiler refusal, not a panic.
use std::{fs, path::PathBuf, process::Command};

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("prod-cli-refusal-{}-{nonce}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained CLI refusal fixture: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

#[test]
fn malformed_static_aggregate_is_rejected_without_panic_or_output() {
    let scratch = Scratch::new();
    let input = scratch.0.join("input.ir");
    fs::write(
        &input,
        r#"(module Invalid
      (type "Token" (ctor "Token.mk" (value UInt8)))
      (def invalid () (List (named "Token"))
        (let token (ctor "Token.mk" 256) (ctor "List.cons" token (ctor "List.nil"))))
      (def run ((request Bytes)) Bytes request))"#,
    )
    .unwrap();
    for name in ["README.md", "LICENSE-MIT", "LICENSE-APACHE"] {
        fs::write(scratch.0.join(name), "Compiler refusal fixture.\n").unwrap();
    }
    for kind in ["gen", "cargo", "core-wasm"] {
        let output = scratch.0.join(kind);
        let mut command = Command::new(env!("CARGO_BIN_EXE_prod"));
        command.arg(kind).arg(&input).arg("--output").arg(&output);
        if kind == "cargo" {
            command.args([
                "--name",
                "refusal-fixture",
                "--version",
                "0.1.0",
                "--description",
                "Compiler refusal fixture",
                "--repository",
                "https://example.invalid/fixture",
                "--homepage",
                "https://example.invalid/fixture",
            ]);
            for (option, name) in [
                ("--readme", "README.md"),
                ("--license-mit", "LICENSE-MIT"),
                ("--license-apache", "LICENSE-APACHE"),
            ] {
                command.arg(option).arg(scratch.0.join(name));
            }
        } else if kind == "core-wasm" {
            command.args(["--entry", "run", "--crate-name", "refusal-fixture"]);
        }
        let result = command.output().unwrap();
        assert_eq!(
            result.status.code(),
            Some(1),
            "{kind}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("UnsupportedList"), "{kind}: {error}");
        assert!(
            error.contains("does not fit its declared type"),
            "{kind}: {error}"
        );
        assert!(!error.contains("panicked"), "{kind}: {error}");
        assert!(result.stdout.is_empty(), "{kind} reported success");
        assert!(!output.exists(), "{kind} published partial output");
    }
}
