use crate::{
    analysis::inference::InferencePool,
    ast::Expr,
    lexer, parser,
    runner::{core::Runner, obj::Object},
    std_lib::StdLibDefiner,
};
use chumsky::Parser as ChumskyParser;
use std::rc::Rc;

/// Result type for pipeline operations
pub type PipelineResult<T> = Result<T, PipelineError>;

/// Errors that can occur during compilation pipeline
#[derive(Debug)]
pub enum PipelineError {
    Tokenize,
    Parse(String),
    TypeInference(String),
    ProgramDataCreation(String),
    Runtime(String),
}

impl std::fmt::Display for PipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Tokenize => write!(f, "Tokenization failed"),
            Self::Parse(msg) => write!(f, "Parse error: {msg}"),
            Self::TypeInference(msg) => write!(f, "Type inference error: {msg}"),
            Self::ProgramDataCreation(msg) => write!(f, "Program data creation error: {msg}"),
            Self::Runtime(msg) => write!(f, "Runtime error: {msg}"),
        }
    }
}

impl std::error::Error for PipelineError {}

/// Compilation pipeline that processes source code through all stages
pub struct Pipeline;

impl Pipeline {
    /// Create a new pipeline
    pub fn new() -> Self {
        Self
    }

    /// Compile and execute source code, returning the result
    pub fn compile_and_run(src: &str) -> PipelineResult<Rc<Object>> {
        let ast = Self::compile(src)?;
        Self::run(ast)
    }

    /// Compile source code to AST, performing all static checks
    pub fn compile(src: &str) -> PipelineResult<Rc<Expr>> {
        // Tokenization
        let tokens = lexer::tokenize(src).ok_or(PipelineError::Tokenize)?;
        log::debug!("tokens: {tokens:?}");

        // Parsing
        let ast = parser::program()
            .parse(&tokens)
            .into_result()
            .map_err(|e| PipelineError::Parse(format!("{e:?}")))?;
        log::debug!("AST: {ast:?}");

        // Type inference
        let mut inference_pool = InferencePool::new();
        let _std_lib = StdLibDefiner::new(&mut inference_pool).build();
        
        let inferred = inference_pool
            .infer(ast.clone())
            .map_err(|e| PipelineError::TypeInference(format!("{e}")))?;
        log::debug!(
            "inferred type: {}",
            inference_pool.display(inferred)
        );

        // Program data validation
        inference_pool
            .create_program_data(ast.clone())
            .map_err(|e| PipelineError::ProgramDataCreation(format!("{e}")))?;

        Ok(ast)
    }

    /// Execute compiled AST
    pub fn run(ast: Rc<Expr>) -> PipelineResult<Rc<Object>> {
        let mut inference_pool = InferencePool::new();
        let std_lib = StdLibDefiner::new(&mut inference_pool).build();
        
        let program_data = inference_pool
            .create_program_data(ast.clone())
            .map_err(|e| PipelineError::ProgramDataCreation(format!("{e}")))?;

        log::info!("running program");
        let mut runner = Runner::new(program_data, std_lib);
        let result = runner
            .eval(ast)
            .map_err(|e| PipelineError::Runtime(format!("{e:?}")))?;
        log::info!("program execution completed");

        Ok(result)
    }
}

impl Default for Pipeline {
    fn default() -> Self {
        Self::new()
    }
}
