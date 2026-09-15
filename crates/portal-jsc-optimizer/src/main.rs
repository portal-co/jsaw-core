mod cli;
mod passes;
mod pipeline;

use std::{
    fs,
    io::{self, Read, Write},
    path::Path,
};

use anyhow::{bail, Context, Result};
use clap::Parser;

use crate::{
    cli::Cli,
    passes::{build_plan, format_registry},
    pipeline::BufferedModulePipeline,
};

fn main() -> Result<()> {
    let cli = Cli::parse();
    if cli.list_passes {
        print!("{}", format_registry());
        return Ok(());
    }

    let plan = build_plan(&cli)?;
    let Some(input) = &cli.input else {
        bail!("<INPUT> is required unless --list-passes is supplied");
    };
    let source = read_input(input)?;
    let source_name = input.to_string_lossy();
    let output = BufferedModulePipeline::new(&plan)
        .optimize_source(&source_name, &source)
        .context("optimization failed")?;

    if cli.check {
        return Ok(());
    }
    write_output(&cli.output, &output)
}

fn read_input(path: &Path) -> Result<String> {
    if path == Path::new("-") {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .context("reading standard input failed")?;
        Ok(source)
    } else {
        fs::read_to_string(path).with_context(|| format!("reading {} failed", path.display()))
    }
}

fn write_output(path: &Path, output: &str) -> Result<()> {
    if path == Path::new("-") {
        io::stdout()
            .write_all(output.as_bytes())
            .context("writing standard output failed")?;
        return Ok(());
    }

    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let temporary = parent.join(format!(
        ".{}.jsaw-opt-{}.tmp",
        path.file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("output"),
        std::process::id()
    ));
    fs::write(&temporary, output)
        .with_context(|| format!("writing temporary output {} failed", temporary.display()))?;
    fs::rename(&temporary, path).with_context(|| {
        format!(
            "atomically replacing output {} with {} failed",
            path.display(),
            temporary.display()
        )
    })
}
