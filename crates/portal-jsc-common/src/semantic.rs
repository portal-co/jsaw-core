use crate::*;
bitflags::bitflags! {
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct SemanticFlags: u64{
        const NO_MONKEYPATCHING = 0x1;
        const NO_JIT = 0x2;
        const BITWISE_OR_ABSENT_NAN = 0x4;
        const PLUGIN_AS_TILDE_PLUGIN = 0x8;
        const NO_CRAZY = 0x10;
        const NATIVES = 0x20;
        const ALL_OBJECTS_FROZEN = 0x40;
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
#[non_exhaustive]
pub enum SemanticTarget {
    #[default]
    ECMAScript,
    Simpl(SimplVersion),
    MuJSC(MuJSCVersion),
    Porffor(PorfforVersion),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum MuJSCVersion {}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum PorfforVersion {}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum SimplVersion {
    Legacy,
}
