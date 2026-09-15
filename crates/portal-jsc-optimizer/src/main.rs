mod cli;
mod passes;

use anyhow::{bail, Result};
use clap::Parser;

use crate::{
    cli::Cli,
    passes::{build_plan, format_registry},
};

fn main() -> Result<()> {
    let cli = Cli::parse();
    if cli.list_passes {
        print!("{}", format_registry());
        return Ok(());
    }

    let _plan = build_plan(&cli)?;
    let Some(input) = cli.input else {
        bail!("<INPUT> is required unless --list-passes is supplied");
    };

    bail!(
        "optimization pipeline is not available yet for `{}`; use --list-passes to inspect pass selection",
        input.display()
    )
}
