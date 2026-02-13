use std::path::PathBuf;

use crate::ast::span::Span;
use crate::diagnostics::CompilerError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BuildError {
    #[error("Invalid glob pattern '{pattern}': {error}")]
    InvalidGlob { pattern: String, error: String },
    #[error("Failed to read file '{path}': {error}")]
    FileReadError { path: PathBuf, error: String },
    #[error("Compile error in '{path}': {error}")]
    CompileError { path: PathBuf, error: CompilerError },
    #[error("Module not found: '{module_name}' imported by '{importing_module}' found in '{path}' at '{span}'")]
    ModuleNotFound {
        module_name: String,
        importing_module: String,
        path: PathBuf,
        span: Span,
    },
    #[error("Cycle detected in module imports: {cycle:?}")]
    CycleInModules { cycle: Vec<(String, PathBuf)> },
    #[error("Duplicate module name '{module_name}' found in '{path1}' and '{path2}'")]
    DuplicateModule {
        module_name: String,
        path1: PathBuf,
        path2: PathBuf,
    },
    #[error("Typechecking panicked in module '{module_name}' at '{path}'")]
    TypecheckPanic { path: PathBuf, module_name: String },
}

impl BuildError {
    pub fn code(&self) -> String {
        match self {
            BuildError::InvalidGlob { .. } => "InvalidGlob".into(),
            BuildError::FileReadError { .. } => "FileReadError".into(),
            BuildError::CompileError { error, .. } => format!("CompileError.{}", error.code()),
            BuildError::ModuleNotFound { .. } => "ModuleNotFound".into(),
            BuildError::CycleInModules { .. } => "CycleInModules".into(),
            BuildError::DuplicateModule { .. } => "DuplicateModule".into(),
            BuildError::TypecheckPanic { .. } => "TypecheckPanic".into(),
        }
    }
}