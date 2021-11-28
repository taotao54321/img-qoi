use thiserror::Error;

/// Specialized [`Result`] for `img-qoi` crate.
pub type QoiResult<T> = Result<T, QoiError>;

/// Errors on `img-qoi` crate.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Error)]
pub enum QoiError {
    #[error("decode error: {0}")]
    Decode(String),

    #[error("encode error: {0}")]
    Encode(String),

    #[error("header error: {0}")]
    Header(String),

    #[error("I/O error: {0}")]
    Io(String),
}

impl QoiError {
    pub(crate) fn new_decode(msg: impl Into<String>) -> Self {
        Self::Decode(msg.into())
    }

    pub(crate) fn new_encode(msg: impl Into<String>) -> Self {
        Self::Encode(msg.into())
    }

    pub(crate) fn new_header(msg: impl Into<String>) -> Self {
        Self::Header(msg.into())
    }
}

// implement this manually to make PartialEq available.
impl From<std::io::Error> for QoiError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e.to_string())
    }
}
