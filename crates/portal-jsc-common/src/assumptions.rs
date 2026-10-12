//! Canonical, portable compiler assumptions.
use alloc::{string::String, vec::Vec};
use core::fmt;
use sha3::{Digest, Sha3_256};
use crate::semantic::SemanticFlags;

/// Version of the stable assumption vocabulary.
pub const REGISTRY_VERSION: u16 = 1;

/// Stable identifiers for the assumptions understood by this release.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(u8)]
pub enum AssumptionId {
    NoMonkeypatching = 1, NoJit = 2, BitwiseOrAbsentNan = 3,
    PluginAsTildePlugin = 4, NoCrazy = 5, Natives = 6,
    AllObjectsFrozen = 7, FunctionPropertiesSealed = 8,
}
impl AssumptionId {
    pub const ALL: [Self; 8] = [Self::NoMonkeypatching, Self::NoJit, Self::BitwiseOrAbsentNan,
        Self::PluginAsTildePlugin, Self::NoCrazy, Self::Natives, Self::AllObjectsFrozen,
        Self::FunctionPropertiesSealed];
    pub const fn name(self) -> &'static str { match self {
        Self::NoMonkeypatching => "no_monkeypatching", Self::NoJit => "no_jit",
        Self::BitwiseOrAbsentNan => "bitwise_or_absent_nan", Self::PluginAsTildePlugin => "plugin_as_tilde_plugin",
        Self::NoCrazy => "no_crazy", Self::Natives => "natives", Self::AllObjectsFrozen => "all_objects_frozen",
        Self::FunctionPropertiesSealed => "function_properties_sealed",
    }}
    pub const fn flag(self) -> SemanticFlags { match self {
        Self::NoMonkeypatching => SemanticFlags::NO_MONKEYPATCHING, Self::NoJit => SemanticFlags::NO_JIT,
        Self::BitwiseOrAbsentNan => SemanticFlags::BITWISE_OR_ABSENT_NAN, Self::PluginAsTildePlugin => SemanticFlags::PLUGIN_AS_TILDE_PLUGIN,
        Self::NoCrazy => SemanticFlags::NO_CRAZY, Self::Natives => SemanticFlags::NATIVES,
        Self::AllObjectsFrozen => SemanticFlags::ALL_OBJECTS_FROZEN, Self::FunctionPropertiesSealed => SemanticFlags::FUNCTION_PROPERTIES_SEALED,
    }}
}

/// A set of requested assumptions. Ordering is canonicalized on construction/resolution.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AssumptionSet { ids: Vec<AssumptionId> }
impl AssumptionSet {
    pub fn new<I: IntoIterator<Item=AssumptionId>>(ids: I) -> Self { let mut v: Vec<_> = ids.into_iter().collect(); v.sort(); v.dedup(); Self { ids: v } }
    pub fn empty() -> Self { Self::default() }
    pub fn ids(&self) -> &[AssumptionId] { &self.ids }
    pub fn semantic_flags(&self) -> SemanticFlags { self.ids.iter().fold(SemanticFlags::empty(), |f, i| f | i.flag()) }
    pub fn canonical_bytes(&self) -> Vec<u8> { let mut b = b"portal-jsc-assumptions\0".to_vec(); b.extend_from_slice(&REGISTRY_VERSION.to_be_bytes()); for i in &self.ids { b.push(*i as u8); } b }
    pub fn digest(&self) -> String { let d = Sha3_256::digest(self.canonical_bytes()); let mut s=String::new(); for x in d { s.push(format_hex(x >> 4)); s.push(format_hex(x & 0xf)); } s }
}
fn format_hex(x: u8) -> char { match x { 0..=9 => (b'0'+x) as char, _ => (b'a' + (x - 10)) as char } }

/// Registry that resolves and projects canonical assumption sets.
#[derive(Clone, Copy, Debug, Default)]
pub struct AssumptionRegistry;
impl AssumptionRegistry {
    pub const fn new() -> Self { Self }
    pub const fn version(&self) -> u16 { REGISTRY_VERSION }
    pub fn resolve<I: IntoIterator<Item=AssumptionId>>(&self, ids: I) -> AssumptionSet { AssumptionSet::new(ids) }
    pub fn project(&self, set: &AssumptionSet) -> SemanticFlags { set.semantic_flags() }
    pub fn name(&self, id: AssumptionId) -> &'static str { id.name() }
}
impl fmt::Display for AssumptionId { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str(self.name()) } }

#[cfg(test)]
mod tests { use super::*;
 #[test] fn canonical_order_and_projection() { let r=AssumptionRegistry::new(); let s=r.resolve([AssumptionId::Natives,AssumptionId::NoJit]); assert_eq!(s.ids(), &[AssumptionId::NoJit,AssumptionId::Natives]); assert_eq!(r.project(&s), SemanticFlags::NO_JIT|SemanticFlags::NATIVES); }
 #[test] fn digest_is_sha3() { assert_eq!(AssumptionSet::empty().digest(), "404309b1820b59368a5e33a5d0277e92ee25b7c7a12c01a07d3fdf7f4fa4082f"); }
}
