use std::collections::{BTreeMap, BTreeSet};

use anyhow::{bail, Context, Result};
use portal_jsc_common::semantic::SemanticFlags;
use portal_jsc_swc_util::SemanticCfg;

use crate::cli::{Cli, Intensity};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Layer {
    Tac,
    Ssa,
}

impl Layer {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Tac => "tac",
            Self::Ssa => "ssa",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntensitySupport {
    Fixed,
    Bounded,
}

impl IntensitySupport {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Fixed => "fixed",
            Self::Bounded => "bounded",
        }
    }
}

/// One stable command-line selectable optimization pass.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PassDescriptor {
    pub name: &'static str,
    pub layer: Layer,
    pub default_enabled: bool,
    pub intensity: IntensitySupport,
    pub summary: &'static str,
}

const DESCRIPTORS: &[PassDescriptor] = &[
    PassDescriptor {
        name: "tac.simplify-justs",
        layer: Layer::Tac,
        default_enabled: true,
        intensity: IntensitySupport::Bounded,
        summary: "Eliminate TAC aliases.",
    },
    PassDescriptor {
        name: "ssa.const-propagate",
        layer: Layer::Ssa,
        default_enabled: true,
        intensity: IntensitySupport::Bounded,
        summary: "Fold standard-semantics constants.",
    },
    PassDescriptor {
        name: "ssa.simplify-conditions",
        layer: Layer::Ssa,
        default_enabled: true,
        intensity: IntensitySupport::Bounded,
        summary: "Replace constant conditional branches.",
    },
    PassDescriptor {
        name: "ssa.simplify-loads",
        layer: Layer::Ssa,
        default_enabled: true,
        intensity: IntensitySupport::Bounded,
        summary: "Eliminate loads proven redundant across side-effect barriers.",
    },
    PassDescriptor {
        name: "ssa.simplify-justs",
        layer: Layer::Ssa,
        default_enabled: true,
        intensity: IntensitySupport::Bounded,
        summary: "Eliminate SSA aliases.",
    },
    PassDescriptor {
        name: "ssa.equate-items",
        layer: Layer::Ssa,
        default_enabled: false,
        intensity: IntensitySupport::Fixed,
        summary: "Substitute SSA aliases through block-edge arguments.",
    },
    PassDescriptor {
        name: "ssa.strip-useless",
        layer: Layer::Ssa,
        default_enabled: false,
        intensity: IntensitySupport::Fixed,
        summary: "Remove unreferenced literal, function, and undefined SSA values.",
    },
    PassDescriptor {
        name: "ssa.inline-iifes",
        layer: Layer::Ssa,
        default_enabled: false,
        intensity: IntensitySupport::Bounded,
        summary: "Inline eligible direct single-block IIFEs.",
    },
    PassDescriptor {
        name: "tac.strip-useless",
        layer: Layer::Tac,
        default_enabled: false,
        intensity: IntensitySupport::Fixed,
        summary: "Remove unreferenced literal, function, and undefined TAC values.",
    },
];

pub fn descriptors() -> &'static [PassDescriptor] {
    DESCRIPTORS
}

pub struct OptimizationPlan {
    selected: BTreeSet<&'static str>,
    intensities: BTreeMap<&'static str, Intensity>,
    semantic: SemanticCfg,
}

impl OptimizationPlan {
    pub fn selected(&self, descriptor: PassDescriptor) -> bool {
        self.selected.contains(descriptor.name)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.selected.contains(name)
    }

    pub fn intensity_for(&self, descriptor: PassDescriptor) -> Option<Intensity> {
        (descriptor.intensity == IntensitySupport::Bounded)
            .then(|| self.intensities[descriptor.name])
    }

    pub fn fixed_point_cap(&self, descriptor: PassDescriptor) -> usize {
        self.intensity_for(descriptor)
            .map(Intensity::fixed_point_cap)
            .unwrap_or(1)
    }

    pub fn semantic(&self) -> &SemanticCfg {
        &self.semantic
    }

    pub fn ordered(&self) -> impl Iterator<Item = PassDescriptor> + '_ {
        descriptors()
            .iter()
            .copied()
            .filter(|pass| self.selected(*pass))
    }
}

pub fn build_plan(cli: &Cli) -> Result<OptimizationPlan> {
    if cli.passes.is_empty() && cli.pass_list.is_none() {
        // No explicit selection: begin with the reviewed standard-semantics defaults.
    }

    let explicit = !cli.passes.is_empty() || cli.pass_list.is_some();
    let mut selected = if explicit {
        BTreeSet::new()
    } else {
        descriptors()
            .iter()
            .filter(|pass| pass.default_enabled)
            .map(|pass| pass.name)
            .collect()
    };

    for name in cli
        .passes
        .iter()
        .map(String::as_str)
        .chain(cli.pass_list.iter().flat_map(|list| list.split(',')))
    {
        selected.insert(require_pass(name)?.name);
    }
    for name in &cli.exclude_pass {
        selected.remove(require_pass(name)?.name);
    }

    let mut intensities = BTreeMap::new();
    for descriptor in descriptors() {
        if selected.contains(descriptor.name) && descriptor.intensity == IntensitySupport::Bounded {
            intensities.insert(descriptor.name, cli.intensity);
        }
    }
    let mut overridden = BTreeSet::new();
    for override_spec in &cli.pass_intensity {
        let (name, intensity) = override_spec
            .split_once('=')
            .context("--pass-intensity must use PASS=LEVEL")?;
        let descriptor = require_pass(name)?;
        if !selected.contains(descriptor.name) {
            bail!("--pass-intensity names unselected pass `{name}`");
        }
        if descriptor.intensity != IntensitySupport::Bounded {
            bail!("pass `{name}` has fixed intensity");
        }
        let intensity = parse_intensity(intensity)?;
        if !overridden.insert(descriptor.name) {
            let prior = intensities[descriptor.name];
            if prior != intensity {
                bail!("conflicting intensity overrides for pass `{name}`");
            }
        }
        intensities.insert(descriptor.name, intensity);
    }

    let mut flags = SemanticFlags::empty();
    for name in &cli.semantic_flag {
        let flag = parse_semantic_flag(name)?;
        if flags.contains(flag) {
            bail!("semantic flag `{name}` was supplied more than once");
        }
        flags.insert(flag);
    }

    Ok(OptimizationPlan {
        selected,
        intensities,
        semantic: {
            let mut semantic = SemanticCfg::default();
            semantic.flags = flags;
            semantic
        },
    })
}

fn require_pass(name: &str) -> Result<PassDescriptor> {
    descriptors()
        .iter()
        .copied()
        .find(|pass| pass.name == name)
        .with_context(|| format!("unknown optimization pass `{name}`"))
}

fn parse_intensity(value: &str) -> Result<Intensity> {
    match value {
        "conservative" => Ok(Intensity::Conservative),
        "standard" => Ok(Intensity::Standard),
        "aggressive" => Ok(Intensity::Aggressive),
        _ => bail!("unknown intensity `{value}`; expected conservative, standard, or aggressive"),
    }
}

fn parse_semantic_flag(value: &str) -> Result<SemanticFlags> {
    match value {
        "no-monkeypatching" => Ok(SemanticFlags::NO_MONKEYPATCHING),
        "no-jit" => Ok(SemanticFlags::NO_JIT),
        "bitwise-or-absent-nan" => Ok(SemanticFlags::BITWISE_OR_ABSENT_NAN),
        "plugin-as-tilde-plugin" => Ok(SemanticFlags::PLUGIN_AS_TILDE_PLUGIN),
        "no-crazy" => Ok(SemanticFlags::NO_CRAZY),
        "natives" => Ok(SemanticFlags::NATIVES),
        "all-objects-frozen" => Ok(SemanticFlags::ALL_OBJECTS_FROZEN),
        "function-properties-sealed" => Ok(SemanticFlags::FUNCTION_PROPERTIES_SEALED),
        _ => bail!("unknown semantic flag `{value}`"),
    }
}

pub fn format_registry() -> String {
    let mut output = String::from("name\tlayer\tdefault\tintensity\tsummary\n");
    for pass in descriptors() {
        output.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\n",
            pass.name,
            pass.layer.as_str(),
            if pass.default_enabled { "yes" } else { "no" },
            pass.intensity.as_str(),
            pass.summary
        ));
    }
    output
}

#[cfg(test)]
mod tests {
    use clap::Parser;

    use super::*;

    fn cli(args: &[&str]) -> Cli {
        Cli::try_parse_from(args).expect("CLI should parse")
    }

    #[test]
    fn defaults_select_only_reviewed_passes() {
        let plan = build_plan(&cli(&["jsaw-opt", "input.mjs"])).unwrap();
        assert_eq!(
            plan.ordered().map(|pass| pass.name).collect::<Vec<_>>(),
            vec![
                "tac.simplify-justs",
                "ssa.const-propagate",
                "ssa.simplify-conditions",
                "ssa.simplify-loads",
                "ssa.simplify-justs",
            ]
        );
    }

    #[test]
    fn explicit_passes_replace_defaults_and_registry_order_wins() {
        let plan = build_plan(&cli(&[
            "jsaw-opt",
            "--pass",
            "ssa.simplify-justs,tac.strip-useless",
            "input.mjs",
        ]))
        .unwrap();
        assert_eq!(
            plan.ordered().map(|pass| pass.name).collect::<Vec<_>>(),
            vec!["ssa.simplify-justs", "tac.strip-useless"]
        );
    }

    #[test]
    fn rejects_conflicting_intensities() {
        let result = build_plan(&cli(&[
            "jsaw-opt",
            "--pass",
            "ssa.simplify-justs",
            "--pass-intensity",
            "ssa.simplify-justs=conservative",
            "--pass-intensity",
            "ssa.simplify-justs=aggressive",
            "input.mjs",
        ]));
        assert!(result
            .err()
            .is_some_and(|error| error.to_string().contains("conflicting intensity")));
    }
}
