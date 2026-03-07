/// Errors that can occur during SSA construction or rewriting.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// A required SSA value was not found in the current context.
    #[error("missing SSA value: {context}")]
    MissingValue { context: &'static str },
    /// An error propagated from TAC construction.
    #[error(transparent)]
    Tac(#[from] swc_tac::Error),
}
