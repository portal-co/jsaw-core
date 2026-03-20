/// Errors that can occur during CFG construction.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// A `break` or `continue` statement was encountered outside any loop/label context.
    #[error("no enclosing loop context (break/continue outside loop)")]
    NoLoopContext,
    /// A module-level syntax construct that is not supported by this IR was encountered.
    #[error("unsupported module-level syntax at {file}:{line}")]
    UnsupportedSyntax { file: &'static str, line: u32 },
}

impl From<std::convert::Infallible> for Error {
    fn from(e: std::convert::Infallible) -> Self {
        match e {}
    }
}
