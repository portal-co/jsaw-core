use std::path::PathBuf;

use clap::{ArgAction, Parser, ValueEnum};

/// Optimize one ECMAScript module through jsaw-core's TAC and SSA IRs.
#[derive(Debug, Parser)]
#[command(name = "jsaw-opt", version, about)]
pub struct Cli {
    /// Input ECMAScript module path; use `-` for standard input.
    pub input: Option<PathBuf>,

    /// Output module path; use `-` for standard output.
    #[arg(short, long, default_value = "-")]
    pub output: PathBuf,

    /// Select exactly this pass set. May be repeated or comma-separated.
    #[arg(long = "pass", value_delimiter = ',')]
    pub passes: Vec<String>,

    /// Comma-separated replacement for the default pass set.
    #[arg(long, conflicts_with = "passes")]
    pub pass_list: Option<String>,

    /// Remove a pass from the resulting selected set. May be repeated or comma-separated.
    #[arg(long, value_delimiter = ',')]
    pub exclude_pass: Vec<String>,

    /// Default intensity for passes that support a bounded intensity budget.
    #[arg(long, value_enum, default_value_t = Intensity::Standard)]
    pub intensity: Intensity,

    /// Per-pass intensity override in PASS=LEVEL form. May be repeated.
    #[arg(long, value_name = "PASS=LEVEL")]
    pub pass_intensity: Vec<String>,

    /// Enable a named semantic assumption required by selected opt-in passes.
    #[arg(long, value_delimiter = ',')]
    pub semantic_flag: Vec<String>,

    /// Print the stable pass registry and exit without reading input.
    #[arg(long)]
    pub list_passes: bool,

    /// Optimize and validate input but do not write output.
    #[arg(long)]
    pub check: bool,

    /// Write debug-only IR snapshots to this directory.
    #[arg(long)]
    pub emit_ir: Option<PathBuf>,

    /// Accepted input syntax. The initial release supports ECMAScript only.
    #[arg(long, value_enum, default_value_t = InputSyntax::Ecmascript)]
    pub syntax: InputSyntax,

    /// Emit pipeline diagnostics to standard error.
    #[arg(short, long, action = ArgAction::Count)]
    pub verbose: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum InputSyntax {
    Ecmascript,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, ValueEnum)]
pub enum Intensity {
    Conservative,
    Standard,
    Aggressive,
}

impl Intensity {
    pub const fn fixed_point_cap(self) -> usize {
        match self {
            Self::Conservative => 1,
            Self::Standard => 4,
            Self::Aggressive => 12,
        }
    }
}
