//! Test fixture producer: synthetic IR probes, not a modeled application.
use prod_codegen::{
    generate_cargo_package, generate_text_view_v1, CargoPackageSpec, GeneratedPackage, PackageFile,
    TextBrowserAdapterBinding, TextViewV1,
};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::{error::Error, fs, path::Path};

fn write(root: &Path, files: &[PackageFile]) -> Result<(), Box<dyn Error>> {
    for file in files {
        let path = root.join(&file.path);
        fs::create_dir_all(path.parent().ok_or("file parent")?)?;
        fs::write(path, &file.bytes)?;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let destination = std::env::args()
        .nth(1)
        .ok_or("expected nonexistent destination")?;
    let root = Path::new(&destination);
    fs::create_dir(root)?;
    let ir = r#"(module TextFixture
      (def invoke ((input Bytes)) Bytes input)
      (def invalid ((_input Bytes)) Bytes
        (cases (slice (utf8-encode (string "é")) 0 1)
          (alt "Option.some" (value) value)
          (alt "Option.none" () (utf8-encode (string "")))))
      (def oversized ((input Bytes)) Bytes (append input input)))"#;
    let (_, module) = parse_module(ir).map_err(|error| format!("parse fixture: {error}"))?;
    let core = generate_cargo_package(
        &module,
        &CargoPackageSpec {
            name: "text-view-core".into(),
            version: "0.1.0".into(),
            description: "Synthetic byte-transport test probes".into(),
            repository: "https://example.invalid/text-view-core".into(),
            homepage: "https://example.invalid/text-view-core/".into(),
            readme: "# Test fixture, not an application\n".into(),
            license_mit: include_str!("../tests/fixtures/LICENSE-MIT").into(),
            license_apache: fs::read_to_string(
                std::env::args()
                    .nth(2)
                    .ok_or("expected Apache license input")?,
            )?,
            input_sha256: format!("{:x}", Sha256::digest(ir.as_bytes())),
            dependencies: vec![],
        },
    )
    .map_err(|error| format!("generate core: {error}"))?;
    write(&root.join("core"), &core.files)?;
    let view = TextViewV1 {
        title: "Text <request>".into(),
        heading: "Request & response".into(),
        input_label: "Request".into(),
        submit_label: "Submit".into(),
        output_label: "Response".into(),
        input_error: "Invalid input".into(),
        response_error: "Invalid response".into(),
        max_input_bytes: 32,
        max_output_bytes: 32,
        model_id: "11".repeat(32),
        view_model_id: "22".repeat(32),
        generated_core_sha256: format!(
            "{:x}",
            Sha256::digest(
                &core
                    .files
                    .iter()
                    .find(|file| file.path == "src/lib.rs")
                    .ok_or("core source")?
                    .bytes
            )
        ),
    };
    for function in ["invoke", "invalid", "oversized"] {
        let binding = TextBrowserAdapterBinding {
            package_name: format!("text-view-{function}"),
            package_version: "0.1.0".into(),
            core_crate_name: "text-view-core".into(),
            core_crate_version: "0.1.0".into(),
            core_function: function.into(),
        };
        let generated = generate_text_view_v1(&view, &binding)
            .map_err(|error| format!("generate view: {error}"))?;
        let second = generate_text_view_v1(&view, &binding)
            .map_err(|error| format!("regenerate view: {error}"))?;
        if generated != second {
            return Err("nondeterministic fixture generation".into());
        }
        let directory = root.join(function);
        write(&directory.join("browser"), &generated.browser_assets)?;
        write(&directory.join("hologram"), &generated.hologram_assets)?;
        write(&directory.join("hologram"), &[generated.hologram_bundle])?;
        let GeneratedPackage { files } = generated.browser_adapter;
        write(&directory.join("adapter"), &files)?;
        write(&directory, &[generated.view_manifest])?;
    }
    Ok(())
}
