//! Canonical, portable compiler assumptions.
//!
//! The registry is deliberately independent of the command line and manifest
//! formats.  Callers resolve external names here before projecting them to the
//! legacy [`SemanticFlags`] bit set.

use alloc::{string::String, vec::Vec};
use core::fmt;
use sha3::{Digest, Sha3_256};

use crate::semantic::SemanticFlags;

/// Version of the canonical wire schema.
pub const SCHEMA_VERSION: u16 = 1;
/// Version of the stable assumption vocabulary.
pub const REGISTRY_VERSION: u16 = 1;
const DOMAIN: &[u8] = b"portal-jsc-assumptions\0";

/// Stable identifiers for assumptions understood by this release.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(u8)]
pub enum AssumptionId {
    NoMonkeypatching = 1,
    NoJit = 2,
    BitwiseOrAbsentNan = 3,
    PluginAsTildePlugin = 4,
    NoCrazy = 5,
    Natives = 6,
    AllObjectsFrozen = 7,
    FunctionPropertiesSealed = 8,
}

impl AssumptionId {
    /// All identifiers in their stable identifier order.
    pub const ALL: [Self; 8] = [
        Self::NoMonkeypatching,
        Self::NoJit,
        Self::BitwiseOrAbsentNan,
        Self::PluginAsTildePlugin,
        Self::NoCrazy,
        Self::Natives,
        Self::AllObjectsFrozen,
        Self::FunctionPropertiesSealed,
    ];

    /// The stable, externally visible identifier.  These names are part of the
    /// schema; in particular, they are hyphenated rather than Rust-style names.
    pub const fn name(self) -> &'static str {
        match self {
            Self::NoMonkeypatching => "no-monkeypatching",
            Self::NoJit => "no-jit",
            Self::BitwiseOrAbsentNan => "bitwise-or-absent-nan",
            Self::PluginAsTildePlugin => "plugin-as-tilde-plugin",
            Self::NoCrazy => "no-crazy",
            Self::Natives => "natives",
            Self::AllObjectsFrozen => "all-objects-frozen",
            Self::FunctionPropertiesSealed => "function-properties-sealed",
        }
    }

    pub const fn flag(self) -> SemanticFlags {
        match self {
            Self::NoMonkeypatching => SemanticFlags::NO_MONKEYPATCHING,
            Self::NoJit => SemanticFlags::NO_JIT,
            Self::BitwiseOrAbsentNan => SemanticFlags::BITWISE_OR_ABSENT_NAN,
            Self::PluginAsTildePlugin => SemanticFlags::PLUGIN_AS_TILDE_PLUGIN,
            Self::NoCrazy => SemanticFlags::NO_CRAZY,
            Self::Natives => SemanticFlags::NATIVES,
            Self::AllObjectsFrozen => SemanticFlags::ALL_OBJECTS_FROZEN,
            Self::FunctionPropertiesSealed => SemanticFlags::FUNCTION_PROPERTIES_SEALED,
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|id| id.name() == name)
    }
}

/// A parameter which is already in its canonical textual representation.
///
/// Parameters are opaque to the registry but are included byte-for-byte in
/// canonical encodings.  This keeps the schema extensible without allowing a
/// platform-dependent serialization to affect identity.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct CanonicalParameter(String);

impl CanonicalParameter {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for CanonicalParameter {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl From<String> for CanonicalParameter {
    fn from(value: String) -> Self {
        Self::new(value)
    }
}

/// An external request.  Keeping the name, rather than only an enum, lets the
/// resolver report unknown names without collapsing them into a generic error.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct AssumptionRequest {
    name: String,
    parameter: Option<CanonicalParameter>,
}

impl AssumptionRequest {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            parameter: None,
        }
    }

    pub fn with_parameter(
        name: impl Into<String>,
        parameter: impl Into<CanonicalParameter>,
    ) -> Self {
        Self {
            name: name.into(),
            parameter: Some(parameter.into()),
        }
    }

    pub fn from_id(id: AssumptionId) -> Self {
        Self::new(id.name())
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameter(&self) -> Option<&CanonicalParameter> {
        self.parameter.as_ref()
    }
}

impl From<AssumptionId> for AssumptionRequest {
    fn from(id: AssumptionId) -> Self {
        Self::from_id(id)
    }
}

impl From<&str> for AssumptionRequest {
    fn from(name: &str) -> Self {
        Self::new(name)
    }
}

impl From<String> for AssumptionRequest {
    fn from(name: String) -> Self {
        Self::new(name)
    }
}

/// A structured, fail-closed resolution diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssumptionDiagnostic {
    Unknown {
        name: String,
        index: usize,
    },
    Duplicate {
        name: String,
        index: usize,
        first_index: usize,
    },
    Conflict {
        name: String,
        index: usize,
        conflicts_with: String,
        conflict_index: usize,
        reason: String,
    },
    Unsupported {
        name: String,
        index: usize,
        reason: String,
    },
    Unfulfilled {
        name: String,
        index: usize,
        reason: String,
    },
}

impl AssumptionDiagnostic {
    fn index(&self) -> usize {
        match self {
            Self::Unknown { index, .. }
            | Self::Duplicate { index, .. }
            | Self::Conflict { index, .. }
            | Self::Unsupported { index, .. }
            | Self::Unfulfilled { index, .. } => *index,
        }
    }
}

fn diagnostic_rank(diagnostic: &AssumptionDiagnostic) -> u8 {
    match diagnostic {
        AssumptionDiagnostic::Unknown { .. } => 0,
        AssumptionDiagnostic::Duplicate { .. } => 1,
        AssumptionDiagnostic::Conflict { .. } => 2,
        AssumptionDiagnostic::Unsupported { .. } => 3,
        AssumptionDiagnostic::Unfulfilled { .. } => 4,
    }
}

/// Failure returned by [`AssumptionRegistry::resolve`].  All diagnostics are
/// retained and sorted deterministically; no partially effective set exists.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssumptionError {
    diagnostics: Vec<AssumptionDiagnostic>,
}

impl AssumptionError {
    pub fn diagnostics(&self) -> &[AssumptionDiagnostic] {
        &self.diagnostics
    }
}

impl fmt::Display for AssumptionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} assumption request(s) could not be resolved",
            self.diagnostics.len()
        )
    }
}

/// A resolved set, retaining both what was requested and what is effective.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AssumptionSet {
    requested: Vec<AssumptionRequest>,
    effective: Vec<AssumptionRequest>,
    requested_ids: Vec<AssumptionId>,
    effective_ids: Vec<AssumptionId>,
}

impl AssumptionSet {
    /// Construct a set without resolving names.  Unlike the old implementation,
    /// this never deduplicates input; use a registry to obtain a validated set.
    pub fn new<I, R>(requests: I) -> Self
    where
        I: IntoIterator<Item = R>,
        R: Into<AssumptionRequest>,
    {
        let mut requested: Vec<_> = requests.into_iter().map(Into::into).collect();
        requested.sort_by(request_order);
        let requested_ids: Vec<AssumptionId> = requested
            .iter()
            .filter_map(|r| AssumptionId::from_name(r.name()))
            .collect();
        Self {
            effective: requested.clone(),
            effective_ids: requested_ids.clone(),
            requested,
            requested_ids,
        }
    }

    pub fn empty() -> Self {
        Self::default()
    }

    /// Effective IDs retained for compatibility with the original API.
    pub fn ids(&self) -> &[AssumptionId] {
        &self.effective_ids
    }

    pub fn requested(&self) -> &[AssumptionRequest] {
        &self.requested
    }

    pub fn effective(&self) -> &[AssumptionRequest] {
        &self.effective
    }

    pub fn requested_ids(&self) -> &[AssumptionId] {
        &self.requested_ids
    }

    pub fn effective_ids(&self) -> &[AssumptionId] {
        &self.effective_ids
    }

    pub fn semantic_flags(&self) -> SemanticFlags {
        self.effective_ids
            .iter()
            .fold(SemanticFlags::empty(), |flags, id| flags | id.flag())
    }

    /// Deterministic, length-delimited canonical representation.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::from(DOMAIN);
        bytes.extend_from_slice(&SCHEMA_VERSION.to_be_bytes());
        bytes.extend_from_slice(&REGISTRY_VERSION.to_be_bytes());
        encode_requests(&mut bytes, &self.requested);
        encode_requests(&mut bytes, &self.effective);
        bytes
    }

    pub fn digest_bytes(&self) -> [u8; 32] {
        Sha3_256::digest(self.canonical_bytes()).into()
    }

    /// Lowercase hexadecimal SHA3-256 digest of [`Self::canonical_bytes`].
    pub fn digest(&self) -> String {
        self.digest_bytes()
            .iter()
            .flat_map(|byte| [hex(byte >> 4), hex(byte & 0xf)])
            .collect()
    }
}

fn request_order(left: &AssumptionRequest, right: &AssumptionRequest) -> core::cmp::Ordering {
    match (
        AssumptionId::from_name(left.name()),
        AssumptionId::from_name(right.name()),
    ) {
        (Some(left_id), Some(right_id)) => left_id
            .cmp(&right_id)
            .then_with(|| left.parameter.cmp(&right.parameter)),
        (Some(_), None) => core::cmp::Ordering::Less,
        (None, Some(_)) => core::cmp::Ordering::Greater,
        (None, None) => left.cmp(right),
    }
}

fn encode_requests(bytes: &mut Vec<u8>, requests: &[AssumptionRequest]) {
    bytes.extend_from_slice(&(requests.len() as u32).to_be_bytes());
    for request in requests {
        let name = request.name.as_bytes();
        bytes.extend_from_slice(&(name.len() as u32).to_be_bytes());
        bytes.extend_from_slice(name);
        match &request.parameter {
            Some(parameter) => {
                bytes.push(1);
                let value = parameter.0.as_bytes();
                bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
                bytes.extend_from_slice(value);
            }
            None => bytes.push(0),
        }
    }
}

fn hex(value: u8) -> char {
    match value {
        0..=9 => (b'0' + value) as char,
        _ => (b'a' + value - 10) as char,
    }
}

/// Resolution policy used by a registry.  The default preserves the legacy
/// behavior: every known assumption is supported and fulfilled, and no flags
/// are enabled by default.
#[derive(Clone, Debug)]
pub struct ResolutionPolicy {
    supported: Vec<AssumptionId>,
    fulfilled: Vec<AssumptionId>,
    defaults: Vec<AssumptionId>,
    conflicts: Vec<(AssumptionId, AssumptionId)>,
}

impl Default for ResolutionPolicy {
    fn default() -> Self {
        Self::new()
    }
}

impl ResolutionPolicy {
    pub fn new() -> Self {
        Self {
            supported: AssumptionId::ALL.into(),
            fulfilled: AssumptionId::ALL.into(),
            defaults: Vec::new(),
            conflicts: Vec::new(),
        }
    }

    pub fn unsupported(mut self, id: AssumptionId) -> Self {
        self.supported.retain(|candidate| *candidate != id);
        self
    }

    pub fn unfulfilled(mut self, id: AssumptionId) -> Self {
        self.fulfilled.retain(|candidate| *candidate != id);
        self
    }

    pub fn default_assumption(mut self, id: AssumptionId) -> Self {
        if !self.defaults.contains(&id) {
            self.defaults.push(id);
        }
        self
    }

    pub fn conflict(mut self, first: AssumptionId, second: AssumptionId) -> Self {
        self.conflicts.push((first, second));
        self
    }
}

/// Registry that resolves external requests and projects canonical sets.
#[derive(Clone, Debug)]
pub struct AssumptionRegistry {
    policy: ResolutionPolicy,
}

impl Default for AssumptionRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl AssumptionRegistry {
    pub fn new() -> Self {
        Self {
            policy: ResolutionPolicy::new(),
        }
    }

    pub fn with_policy(policy: ResolutionPolicy) -> Self {
        Self { policy }
    }

    pub const fn schema_version(&self) -> u16 {
        SCHEMA_VERSION
    }

    pub const fn version(&self) -> u16 {
        REGISTRY_VERSION
    }

    pub fn resolve<I, R>(&self, requests: I) -> Result<AssumptionSet, AssumptionError>
    where
        I: IntoIterator<Item = R>,
        R: Into<AssumptionRequest>,
    {
        let requests: Vec<AssumptionRequest> = requests.into_iter().map(Into::into).collect();
        let mut diagnostics = Vec::new();
        let mut known: Vec<(usize, AssumptionId)> = Vec::new();

        for (index, request) in requests.iter().enumerate() {
            let Some(id) = AssumptionId::from_name(request.name()) else {
                diagnostics.push(AssumptionDiagnostic::Unknown {
                    name: request.name.clone(),
                    index,
                });
                continue;
            };
            let duplicate = if let Some((first_index, _)) =
                known.iter().find(|(_, first_id)| *first_id == id)
            {
                if requests[*first_index].parameter == request.parameter {
                    diagnostics.push(AssumptionDiagnostic::Duplicate {
                        name: request.name.clone(),
                        index,
                        first_index: *first_index,
                    });
                } else {
                    diagnostics.push(AssumptionDiagnostic::Conflict {
                        name: request.name.clone(),
                        index,
                        conflicts_with: request.name.clone(),
                        conflict_index: *first_index,
                        reason: String::from("different parameters for one assumption"),
                    });
                }
                true
            } else {
                known.push((index, id));
                false
            };
            if !duplicate {
                if !self.policy.supported.contains(&id) {
                    diagnostics.push(AssumptionDiagnostic::Unsupported {
                        name: request.name.clone(),
                        index,
                        reason: String::from("assumption is not supported by this registry"),
                    });
                }
                if !self.policy.fulfilled.contains(&id) {
                    diagnostics.push(AssumptionDiagnostic::Unfulfilled {
                        name: request.name.clone(),
                        index,
                        reason: String::from("assumption prerequisites are not fulfilled"),
                    });
                }
            }
        }

        for &(first_index, first_id) in &known {
            for &(second_index, second_id) in &known {
                if first_index < second_index
                    && self.policy.conflicts.iter().any(|(a, b)| {
                        (*a == first_id && *b == second_id) || (*a == second_id && *b == first_id)
                    })
                {
                    diagnostics.push(AssumptionDiagnostic::Conflict {
                        name: requests[second_index].name.clone(),
                        index: second_index,
                        conflicts_with: requests[first_index].name.clone(),
                        conflict_index: first_index,
                        reason: String::from("assumptions cannot be enabled together"),
                    });
                }
            }
        }

        diagnostics.sort_by(|left, right| {
            left.index()
                .cmp(&right.index())
                .then_with(|| diagnostic_rank(left).cmp(&diagnostic_rank(right)))
        });
        if !diagnostics.is_empty() {
            return Err(AssumptionError { diagnostics });
        }

        let mut requested = requests;
        requested.sort_by(request_order);
        let mut effective = requested.clone();
        for id in &self.policy.defaults {
            let request = AssumptionRequest::from_id(*id);
            if !effective
                .iter()
                .any(|candidate| candidate.name() == request.name())
            {
                effective.push(request);
            }
        }
        effective.sort_by(request_order);
        let requested_ids: Vec<AssumptionId> = requested
            .iter()
            .filter_map(|r| AssumptionId::from_name(r.name()))
            .collect();
        let effective_ids: Vec<AssumptionId> = effective
            .iter()
            .filter_map(|r| AssumptionId::from_name(r.name()))
            .collect();
        Ok(AssumptionSet {
            requested,
            effective,
            requested_ids,
            effective_ids,
        })
    }

    pub fn project(&self, set: &AssumptionSet) -> SemanticFlags {
        set.semantic_flags()
    }

    pub fn name(&self, id: AssumptionId) -> &'static str {
        id.name()
    }
}

impl fmt::Display for AssumptionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_external_hyphenated_identifiers() {
        assert_eq!(AssumptionId::NoMonkeypatching.name(), "no-monkeypatching");
        assert!(AssumptionId::from_name("no_monkeypatching").is_none());
    }

    #[test]
    fn requested_and_effective_sets_are_distinct() {
        let registry = AssumptionRegistry::with_policy(
            ResolutionPolicy::new().default_assumption(AssumptionId::Natives),
        );
        let set = registry.resolve([AssumptionId::NoJit]).unwrap();
        assert_eq!(set.requested_ids(), &[AssumptionId::NoJit]);
        assert_eq!(
            set.effective_ids(),
            &[AssumptionId::NoJit, AssumptionId::Natives]
        );
        assert_eq!(set.requested().len(), 1);
    }

    #[test]
    fn diagnostics_are_structured_and_ordered() {
        let registry = AssumptionRegistry::with_policy(
            ResolutionPolicy::new()
                .unsupported(AssumptionId::NoJit)
                .unfulfilled(AssumptionId::Natives)
                .conflict(AssumptionId::NoCrazy, AssumptionId::Natives),
        );
        let error = registry
            .resolve([
                AssumptionRequest::new("missing"),
                AssumptionRequest::new("no-jit"),
                AssumptionRequest::new("no-jit"),
                AssumptionRequest::new("natives"),
                AssumptionRequest::new("no-crazy"),
            ])
            .unwrap_err();
        assert!(matches!(
            error.diagnostics()[0],
            AssumptionDiagnostic::Unknown { index: 0, .. }
        ));
        assert!(matches!(
            error.diagnostics()[1],
            AssumptionDiagnostic::Unsupported { index: 1, .. }
        ));
        assert!(matches!(
            error.diagnostics()[2],
            AssumptionDiagnostic::Duplicate { index: 2, .. }
        ));
        assert!(matches!(
            error.diagnostics()[3],
            AssumptionDiagnostic::Unfulfilled { index: 3, .. }
        ));
        assert!(matches!(
            error.diagnostics()[4],
            AssumptionDiagnostic::Conflict { index: 4, .. }
        ));
    }

    #[test]
    fn parameter_conflicts_are_not_deduplicated() {
        let error = AssumptionRegistry::new()
            .resolve([
                AssumptionRequest::with_parameter("no-jit", "a"),
                AssumptionRequest::with_parameter("no-jit", "b"),
            ])
            .unwrap_err();
        assert!(matches!(
            error.diagnostics()[0],
            AssumptionDiagnostic::Conflict { .. }
        ));
    }

    #[test]
    fn canonical_order_and_projection_preserve_legacy_flags() {
        let registry = AssumptionRegistry::new();
        let set = registry
            .resolve([AssumptionId::Natives, AssumptionId::NoJit])
            .unwrap();
        assert_eq!(set.ids(), &[AssumptionId::NoJit, AssumptionId::Natives]);
        assert_eq!(
            registry.project(&set),
            SemanticFlags::NO_JIT | SemanticFlags::NATIVES
        );
        assert_eq!(
            registry.project(
                &registry
                    .resolve(core::iter::empty::<AssumptionId>())
                    .unwrap()
            ),
            SemanticFlags::empty()
        );
    }

    #[test]
    fn digest_is_stable_and_length_delimited() {
        let registry = AssumptionRegistry::new();
        let first = registry
            .resolve([AssumptionId::NoJit, AssumptionId::Natives])
            .unwrap();
        let second = registry
            .resolve([AssumptionId::Natives, AssumptionId::NoJit])
            .unwrap();
        assert_eq!(first.canonical_bytes(), second.canonical_bytes());
        assert_eq!(first.digest(), second.digest());
        assert_eq!(first.digest().len(), 64);
        assert_eq!(
            AssumptionSet::empty().digest(),
            "0e4ac136214c1121e2fee705282a1dc4b4222e1efc5d87ca8bc46efd8ba18d27"
        );
    }
}
