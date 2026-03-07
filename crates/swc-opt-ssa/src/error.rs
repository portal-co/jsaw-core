/// Errors that can occur during SSA optimisation passes.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// A required value was not found in the optimisation state.
    #[error("missing value: {context}")]
    MissingValue { context: &'static str },
    /// An error propagated from SSA construction.
    #[error(transparent)]
    Ssa(#[from] swc_ssa::Error),
}
