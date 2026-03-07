/// Errors that can occur during TAC construction.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// An unsupported JavaScript syntax was encountered.
    #[error("unsupported syntax at {file}:{line}")]
    Unsupported {
        file: &'static str,
        line: u32,
    },
    /// An error propagated from CFG construction.
    #[error(transparent)]
    Cfg(#[from] swc_cfg::Error),
}
