//! Utilities for working with SWC (Speedy Web Compiler) ASTs.
//!
//! This crate provides helper functions and traits for working with SWC's JavaScript
//! AST, including semantic analysis, native function resolution, and import mapping.
//!
//! # Key Features
//!
//! - Semantic configuration for controlling compilation behavior
//! - Native function recognition and resolution
//! - Import mapping for module resolution
//! - Constant evaluation for SES (Secure ECMAScript) methods
//!
//! # Main Types
//!
//! - [`SemanticCfg`]: Configuration for semantic analysis
//! - [`ResolveNatives`]: Trait for resolving native/intrinsic functions
//! - [`ImportMapper`]: Trait for custom import resolution

pub use portal_jsc_common as common;
use portal_jsc_common::natives::Native;
pub use portal_jsc_common::{semantic::SemanticFlags, semantic::SemanticTarget, syntax::ImportMap};
use portal_solutions_swibb::ConstCollector;
use std::{collections::BTreeMap, mem::take};
use swc_atoms::{Atom, Wtf8Atom};
use swc_common::{Span, Spanned};
use swc_ecma_ast::{BinaryOp, Bool, CallExpr, Expr, Id, Lit, MemberExpr, MemberProp, ModuleItem};
use swc_ecma_visit::{VisitMut, VisitMutWith};
pub fn ses_method(a: &Lit, b: &str, args: &mut (dyn Iterator<Item = Lit> + '_)) -> Option<Lit> {
    match b {
        "startsWith" if a.is_str() => {
            let a = a.as_str()?;
            let arg = args.next()?;
            let arg = arg.as_str()?;
            Some(Lit::Bool(Bool {
                span: a.span,
                value: a.value.starts_with(arg.value.as_str()?),
            }))
        }
        _ => None,
    }
}
/// Semantic configuration for compilation.
///
/// Combines semantic flags and target information to control how JavaScript
/// code is analyzed and compiled.
///
/// # Fields
///
/// - `flags`: Semantic flags controlling optimization assumptions
/// - `target`: The target JavaScript engine or variant
#[derive(Default, Clone)]
#[non_exhaustive]
pub struct SemanticCfg {
    /// Semantic flags (see `SemanticFlags` in portal-jsc-common)
    pub flags: SemanticFlags,
    /// Target JavaScript engine/variant
    pub target: SemanticTarget,
}

/// Trait for resolving native/intrinsic functions in expressions.
///
/// This trait allows types (typically AST expressions) to be queried for
/// whether they represent a call to a recognized native function.
pub trait ResolveNatives {
    /// Attempts to resolve this expression as a native function call.
    ///
    /// Returns `Some(native)` if this expression is a recognized native function
    /// call, or `None` otherwise.
    ///
    /// # Arguments
    ///
    /// - `cfg`: Semantic configuration
    /// - `import_map`: Import mapper for resolving module imports
    fn resolve_natives(
        &self,
        cfg: &SemanticCfg,
        import_map: &(dyn ImportMapper + '_),
    ) -> Option<Native<&Expr>>;
}
impl ResolveNatives for Expr {
    fn resolve_natives(
        &self,
        _cfg: &SemanticCfg,
        import_map: &(dyn ImportMapper + '_),
    ) -> Option<Native<&Expr>> {
        fn prop<'a>(c: &'a CallExpr, p: &'a Expr) -> Option<Native<&'a Expr>> {
            match p {
                Expr::Lit(Lit::Str(s)) => {
                    let s = s.value.as_str()?.strip_prefix("~Natives_")?;
                    let n = Native::of(s)?;
                    let mut a = c.args.iter();
                    n.map(&mut |_| {
                        let Some(v) = a.next() else {
                            return Err(());
                        };
                        Ok(&*v.expr)
                    })
                    .ok()
                }
                Expr::Assign(a) => prop(c, &a.right),
                _ => None,
            }
        }
        fn member<'a>(c: &'a CallExpr, m: &'a MemberExpr) -> Option<Native<&'a Expr>> {
            match &*m.obj {
                Expr::Ident(i) if i.sym == "globalThis" => match &m.prop {
                    MemberProp::Computed(cp) => prop(c, &cp.expr),
                    _ => None,
                },
                _ => None,
            }
        }
        fn expr<'a>(
            c: &'a CallExpr,
            e: &'a Expr,
            import_map: &(dyn ImportMapper + '_),
        ) -> Option<Native<&'a Expr>> {
            match e {
                Expr::Ident(i) => match import_map.import_of(&i.to_id())? {
                    (a, ImportMap::Named { name })
                        if a == "@portal-solutions/jsaw-intrinsics-base" =>
                    {
                        //  let s = s.value.strip_prefix("~Natives_")?;
                        let n = Native::of(&name)?;
                        let mut a = c.args.iter();
                        n.map(&mut |_| {
                            let Some(v) = a.next() else {
                                return Err(());
                            };
                            Ok(&*v.expr)
                        })
                        .ok()
                    }
                    _ => None,
                },
                Expr::Member(m) => member(c, m),
                Expr::Bin(b) if matches!(b.op, BinaryOp::NullishCoalescing) => {
                    expr(c, &b.left, import_map)
                }
                Expr::OptChain(o) => match &*o.base {
                    swc_ecma_ast::OptChainBase::Member(m) => member(c, m),
                    _ => None,
                },
                _ => None,
            }
        }
        match self {
            Expr::Call(c) => expr(c, &**(c.callee.as_expr()?), import_map),
            _ => None,
        }
    }
}
pub struct InlineTracer<'a> {
    pub mapper: &'a (dyn ImportMapper + 'a),
    pub inlinable: bool,
}
impl<'a> VisitMut for InlineTracer<'a> {
    fn visit_mut_expr(&mut self, node: &mut Expr) {
        node.visit_mut_children_with(self);
        // if let Some(Native::InlineMe) = node.resolve_natives(&*self.mapper) {
        //     self.inlinable = true;
        //     *node = *Expr::undefined(node.span());
        // }
    }
}
pub struct InlineHintInliner<'a> {
    pub consts: &'a ConstCollector,
    pub mapper: &'a (dyn ImportMapper + 'a),
}
impl VisitMut for InlineHintInliner<'_> {
    fn visit_mut_expr(&mut self, node: &mut Expr) {
        let mut not_done = true;
        while take(&mut not_done) {
            if let Expr::Ident(i) = node
                && let Some(mut b) = self.consts.map.get(&i.to_id()).cloned() {
                    let mut t = InlineTracer {
                        mapper: self.mapper,
                        inlinable: false,
                    };
                    b.visit_mut_with(&mut t);
                    if t.inlinable {
                        not_done = true;
                        *node = *b;
                    }
                }
            node.visit_mut_children_with(self);
        }
    }
}
pub mod brighten;
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Natives {
    pub all: BTreeMap<Atom, Id>,
}
#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct MakeSpanned<T> {
    pub value: T,
    pub span: Span,
}
impl<T> Spanned for MakeSpanned<T> {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ImportOr<T> {
    NotImport(T),
    Import {
        value: T,
        module: Atom,
        name: ImportMap<Atom>,
    },
}
impl<T: Default> Default for ImportOr<T> {
    fn default() -> Self {
        Self::NotImport(T::default())
    }
}
impl<T> AsRef<T> for ImportOr<T> {
    fn as_ref(&self) -> &T {
        match self {
            ImportOr::NotImport(value) => value,
            ImportOr::Import {
                value,
                module: _,
                name: _,
            } => value,
        }
    }
}
impl<T> AsMut<T> for ImportOr<T> {
    fn as_mut(&mut self) -> &mut T {
        match self {
            ImportOr::NotImport(value) => value,
            ImportOr::Import {
                value,
                module: _,
                name: _,
            } => value,
        }
    }
}
pub trait Extract<T>: AsRef<T> + AsMut<T> {
    fn extract_own(self) -> T;
}
impl<T> Extract<T> for ImportOr<T> {
    fn extract_own(self) -> T {
        match self {
            ImportOr::NotImport(value) => value,
            ImportOr::Import {
                value,
                module: _,
                name: _,
            } => value,
        }
    }
}
impl<T: AsRef<T> + AsMut<T>> Extract<T> for T {
    fn extract_own(self) -> T {
        self
    }
}
// impl<T, U: Into<T> + AsRef<T> + AsMut<T>> Extract<T> for U {}
pub fn mangle((a, b): &Id) -> Atom {
    Atom::new(format!("{}${a}", b.as_u32()))
}
pub trait ImportMapper {
    fn import_of(&self, cx: &Id) -> Option<(Wtf8Atom, ImportMap<Atom>)>;
}
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NoImportMapper {}
impl ImportMapper for NoImportMapper {
    fn import_of(&self, _cx: &Id) -> Option<(Wtf8Atom, ImportMap<Atom>)> {
        None
    }
}
pub trait ModuleMapper {
    fn item_of(&self, id: &Id) -> Option<&ModuleItem>;
}
#[cfg(feature = "ty")]
pub mod r#type;
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum BreakKind {
    BreakAfter,
    DoNotBreakAfter,
}
// #[cfg(feature = "cli")]
// pub fn cli_load(cm: &Lrc<SourceMap>, fm: &Lrc<SourceFile>) -> Module {
//     // let cm: Lrc<SourceMap> = Default::default();
//     let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));
//     // Real usage
//     // let fm = cm
//     //     .load_file(Path::new("test.js"))
//     //     .expect("failed to load test.js");
//     // let fm = cm.new_source_file(
//     //     FileName::Custom("test.js".into()).into(),
//     //     "function foo() {}".into(),
//     // );
//     let lexer = Lexer::new(
//         // We want to parse ecmascript
//         Syntax::Es(Default::default()),
//         // EsVersion defaults to es5
//         Default::default(),
//         StringInput::from(&**fm),
//         None,
//     );
//     let mut parser = Parser::new_from(lexer);
//     for e in parser.take_errors() {
//         e.into_diagnostic(&handler).emit();
//     }
//     let mut module = parser
//         .parse_module()
//         .map_err(|mut e| {
//             // Unrecoverable fatal error occurred
//             e.into_diagnostic(&handler).emit()
//         })
//         .expect("failed to parser module");
//      module.visit_mut_with(&mut swc_ecma_transforms_base::resolver(
//         Mark::root(),
//         Mark::new(),
//         false,
//     ));
//     return module;
// }
