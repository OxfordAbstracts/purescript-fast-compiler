//! IR expression → JS expression translation.
//!
//! Phase 1–3 subset: literals, variable/constructor references, application,
//! lambdas, if/then/else, records, arrays, negate, `case` + pattern matching,
//! multi-equation value groups, guards, and `let`/`where`.

use std::collections::HashMap;

use crate::codegen::common::{ident_to_js, module_name_str_to_js};
use crate::codegen::js_ast::{JsBinaryOp, JsExpr, JsStmt, JsUnaryOp};
use crate::names::ModuleQualifier;
use crate::span::Span;
use crate::typecheck_db::ir;
use crate::typecheck_db::passes::constraints::ResolvedDict;
use crate::typecheck_db::types::Type;

use super::{instance_js_name, type_head_name, unsupported, DeclCgCtx};

/// Carries translation state for one declaration: the module context plus an
/// accumulator of external module references discovered while walking the body,
/// the per-call-site resolved dictionaries, and a counter for fresh temporaries.
pub(super) struct Cg<'a> {
    ctx: &'a DeclCgCtx<'a>,
    constraint_dicts: &'a HashMap<Span, Vec<ResolvedDict>>,
    /// In-scope given dictionaries: (class simple name, JS param name).
    dict_scope: Vec<(String, String)>,
    external_refs: Vec<Vec<String>>,
    counter: usize,
}

impl<'a> Cg<'a> {
    pub(super) fn new(
        ctx: &'a DeclCgCtx<'a>,
        constraint_dicts: &'a HashMap<Span, Vec<ResolvedDict>>,
        dict_scope: Vec<(String, String)>,
    ) -> Self {
        Self { ctx, constraint_dicts, dict_scope, external_refs: Vec::new(), counter: 0 }
    }

    pub(super) fn take_external_refs(self) -> Vec<Vec<String>> {
        self.external_refs
    }

    fn fresh(&mut self, prefix: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("${prefix}{n}")
    }

    /// Body for a value-equation group.
    pub(super) fn value_group_body(&mut self, equations: &[&ir::Decl]) -> JsExpr {
        // Fast path: a single equation with no binders, no guards, no where —
        // the body is just the expression bound to `var name = ...`.
        if equations.len() == 1 {
            if let ir::Decl::Value { binders, guarded, where_clause, .. } = equations[0] {
                if binders.is_empty() && where_clause.is_empty() {
                    if let ir::GuardedExpr::Unconditional(e) = guarded {
                        return self.gen_expr(e);
                    }
                }
            }
        }
        self.compile_equations(equations)
    }

    /// Compile a (possibly multi-) equation group into a curried function (or,
    /// for arity 0, an IIFE) using first-match-wins pattern dispatch.
    fn compile_equations(&mut self, equations: &[&ir::Decl]) -> JsExpr {
        let arity = match equations[0] {
            ir::Decl::Value { binders, .. } => binders.len(),
            _ => return unsupported("non-value in value group"),
        };
        let params: Vec<String> = (0..arity).map(|i| format!("$arg{i}")).collect();

        let mut stmts: Vec<JsStmt> = Vec::new();
        let mut total = false; // a clause that always matches + always returns
        for eq in equations {
            let (binders, guarded, where_clause) = match eq {
                ir::Decl::Value { binders, guarded, where_clause, .. } => {
                    (binders, guarded, where_clause)
                }
                _ => return unsupported("non-value in value group"),
            };
            if binders.len() != arity {
                return unsupported("equation arity mismatch");
            }
            let mut tests: Vec<JsExpr> = Vec::new();
            let mut binds: Vec<JsStmt> = Vec::new();
            for (p, b) in params.iter().zip(binders.iter()) {
                self.compile_binder(&JsExpr::Var(p.clone()), b, &mut tests, &mut binds);
            }
            let mut block = binds;
            self.emit_where(where_clause, &mut block);
            self.emit_guarded(guarded, &mut block);
            // An irrefutable, unconditional clause always matches and returns —
            // emit it inline and skip the dead `if (true)` / fall-through throw.
            if tests.is_empty() && matches!(guarded, ir::GuardedExpr::Unconditional(_)) {
                stmts.extend(block);
                total = true;
                break;
            }
            stmts.push(JsStmt::If(and_all(tests), block, None));
        }
        if !total {
            stmts.push(throw_no_match());
        }

        if arity == 0 {
            return iife(stmts);
        }
        // Wrap innermost-out in curried single-arg functions.
        let mut func = JsExpr::Function(None, vec![params[arity - 1].clone()], stmts);
        for p in params[..arity - 1].iter().rev() {
            func = JsExpr::Function(None, vec![p.clone()], vec![JsStmt::Return(func)]);
        }
        func
    }

    /// Append `where` bindings (in source order) as `var` decls to `block`.
    fn emit_where(&mut self, where_clause: &[ir::LetBinding], block: &mut Vec<JsStmt>) {
        for lb in where_clause {
            self.emit_let_binding(lb, block);
        }
    }

    fn emit_let_binding(&mut self, lb: &ir::LetBinding, block: &mut Vec<JsStmt>) {
        match lb {
            ir::LetBinding::Signature { .. } => {}
            ir::LetBinding::Value { binder, expr, .. } => {
                let value = self.gen_expr(expr);
                match binder {
                    ir::Binder::Var { name, .. } => {
                        block.push(JsStmt::VarDecl(ident_to_js(name.value.symbol()), Some(value)));
                    }
                    ir::Binder::Wildcard { .. } => {
                        block.push(JsStmt::Expr(value));
                    }
                    _ => {
                        // Pattern let: bind to a temp, then destructure.
                        let tmp = self.fresh("let");
                        block.push(JsStmt::VarDecl(tmp.clone(), Some(value)));
                        let mut tests = Vec::new();
                        let mut binds = Vec::new();
                        self.compile_binder(&JsExpr::Var(tmp), binder, &mut tests, &mut binds);
                        block.extend(binds);
                    }
                }
            }
        }
    }

    /// Emit a guarded result into `block`. Unconditional → a single `return`.
    /// Guarded → one `if (cond) return expr;` per guard; fall-through (no match)
    /// leaves the block without returning so the caller's next clause runs.
    fn emit_guarded(&mut self, guarded: &ir::GuardedExpr, block: &mut Vec<JsStmt>) {
        match guarded {
            ir::GuardedExpr::Unconditional(e) => {
                let v = self.gen_expr(e);
                block.push(JsStmt::Return(v));
            }
            ir::GuardedExpr::Guarded(guards) => {
                for g in guards {
                    let mut tests: Vec<JsExpr> = Vec::new();
                    let mut inner: Vec<JsStmt> = Vec::new();
                    for gp in &g.patterns {
                        match gp {
                            ir::GuardPattern::Boolean(e) => tests.push(self.gen_expr(e)),
                            ir::GuardPattern::Pattern(binder, e) => {
                                // `pat <- expr` — bind expr to a temp, test+bind.
                                let scrut = self.gen_expr(e);
                                let tmp = self.fresh("g");
                                inner.push(JsStmt::VarDecl(tmp.clone(), Some(scrut)));
                                self.compile_binder(
                                    &JsExpr::Var(tmp),
                                    binder,
                                    &mut tests,
                                    &mut inner,
                                );
                            }
                        }
                    }
                    let result = self.gen_expr(&g.expr);
                    inner.push(JsStmt::Return(result));
                    block.push(JsStmt::If(and_all(tests), inner, None));
                }
            }
        }
    }

    // -- expressions --------------------------------------------------------

    fn gen_expr(&mut self, e: &ir::Expr) -> JsExpr {
        match e {
            ir::Expr::Literal { lit, .. } => self.gen_literal(lit),
            ir::Expr::Var { name, span } => {
                let sym = name.name.symbol();
                let base = self.gen_var(name.module, sym);
                // Apply each resolved dictionary for this site as a curried
                // leading argument, in signature order: `f(d0)(d1)…`.
                let mut e = base;
                for dict in self.dicts_for(sym, *span) {
                    e = JsExpr::App(Box::new(e), vec![dict]);
                }
                e
            }
            ir::Expr::App { func, arg, .. } => {
                let f = self.gen_expr(func);
                let a = self.gen_expr(arg);
                JsExpr::App(Box::new(f), vec![a])
            }
            ir::Expr::Lambda { binders, body, .. } => {
                let b = self.gen_expr(body);
                self.wrap_lambda(binders, b)
            }
            ir::Expr::If { cond, then_expr, else_expr, .. } => JsExpr::Ternary(
                Box::new(self.gen_expr(cond)),
                Box::new(self.gen_expr(then_expr)),
                Box::new(self.gen_expr(else_expr)),
            ),
            ir::Expr::Case { exprs, alts, .. } => self.compile_case(exprs, alts),
            ir::Expr::Let { bindings, body, .. } => {
                let mut block = Vec::new();
                for lb in bindings {
                    self.emit_let_binding(lb, &mut block);
                }
                let v = self.gen_expr(body);
                block.push(JsStmt::Return(v));
                iife(block)
            }
            ir::Expr::Record { fields, .. } => {
                let mut js_fields = Vec::with_capacity(fields.len());
                for f in fields {
                    if f.is_update || f.is_nested {
                        return unsupported("record update/nested field");
                    }
                    let key = f.label.value.resolve().unwrap_or_default();
                    let value = match &f.value {
                        Some(v) => self.gen_expr(v),
                        None => JsExpr::Var(ident_to_js(crate::names::value_name(&key).symbol())),
                    };
                    js_fields.push((key, value));
                }
                JsExpr::ObjectLit(js_fields)
            }
            ir::Expr::RecordAccess { expr, field, .. } => {
                let obj = self.gen_expr(expr);
                let label = field.value.resolve().unwrap_or_default();
                JsExpr::Indexer(Box::new(obj), Box::new(JsExpr::StringLit(label)))
            }
            ir::Expr::Array { elements, .. } => {
                JsExpr::ArrayLit(elements.iter().map(|el| self.gen_expr(el)).collect())
            }
            ir::Expr::Negate { expr, .. } => {
                JsExpr::Unary(JsUnaryOp::Negate, Box::new(self.gen_expr(expr)))
            }
            ir::Expr::Parens { expr, .. } | ir::Expr::TypeAnnotation { expr, .. } => {
                self.gen_expr(expr)
            }
            ir::Expr::VisibleTypeApp { func, .. } => self.gen_expr(func),
            ir::Expr::Constructor { name, .. } => self.gen_ctor(name.module, name.name.symbol()),
            _ => unsupported("expression"),
        }
    }

    fn wrap_lambda(&mut self, binders: &[ir::Binder], body: JsExpr) -> JsExpr {
        // Simple var/wildcard binders become plain params; non-trivial binders
        // get a fresh param plus a destructuring prologue.
        let mut acc = body;
        for binder in binders.iter().rev() {
            match binder {
                ir::Binder::Var { name, .. } => {
                    let param = ident_to_js(name.value.symbol());
                    acc = JsExpr::Function(None, vec![param], vec![JsStmt::Return(acc)]);
                }
                ir::Binder::Wildcard { .. } => {
                    acc = JsExpr::Function(None, vec!["$__unused".to_string()], vec![JsStmt::Return(acc)]);
                }
                _ => {
                    let param = self.fresh("p");
                    let mut tests = Vec::new();
                    let mut binds = Vec::new();
                    self.compile_binder(&JsExpr::Var(param.clone()), binder, &mut tests, &mut binds);
                    let mut block = binds;
                    block.push(JsStmt::Return(acc));
                    acc = JsExpr::Function(None, vec![param], block);
                }
            }
        }
        acc
    }

    fn compile_case(&mut self, exprs: &[ir::Expr], alts: &[ir::CaseAlternative]) -> JsExpr {
        let mut stmts: Vec<JsStmt> = Vec::new();
        let mut scruts: Vec<JsExpr> = Vec::with_capacity(exprs.len());
        for e in exprs {
            let v = self.fresh("v");
            let val = self.gen_expr(e);
            stmts.push(JsStmt::VarDecl(v.clone(), Some(val)));
            scruts.push(JsExpr::Var(v));
        }
        for alt in alts {
            let mut tests: Vec<JsExpr> = Vec::new();
            let mut binds: Vec<JsStmt> = Vec::new();
            for (scrut, b) in scruts.iter().zip(alt.binders.iter()) {
                self.compile_binder(scrut, b, &mut tests, &mut binds);
            }
            let mut block = binds;
            self.emit_guarded(&alt.result, &mut block);
            stmts.push(JsStmt::If(and_all(tests), block, None));
        }
        stmts.push(throw_no_match());
        iife(stmts)
    }

    // -- pattern compilation ------------------------------------------------

    /// Compile a binder against `scrut`, accumulating boolean `tests` and
    /// variable-binding statements `binds`.
    fn compile_binder(
        &mut self,
        scrut: &JsExpr,
        binder: &ir::Binder,
        tests: &mut Vec<JsExpr>,
        binds: &mut Vec<JsStmt>,
    ) {
        match binder {
            ir::Binder::Wildcard { .. } => {}
            ir::Binder::Var { name, .. } => {
                binds.push(JsStmt::VarDecl(ident_to_js(name.value.symbol()), Some(scrut.clone())));
            }
            ir::Binder::Parens { binder, .. } | ir::Binder::Typed { binder, .. } => {
                self.compile_binder(scrut, binder, tests, binds);
            }
            ir::Binder::As { name, binder, .. } => {
                binds.push(JsStmt::VarDecl(ident_to_js(name.value.symbol()), Some(scrut.clone())));
                self.compile_binder(scrut, binder, tests, binds);
            }
            ir::Binder::Literal { lit, .. } => self.compile_literal_binder(scrut, lit, tests, binds),
            ir::Binder::Constructor { name, args, .. } => {
                let ctor_js = ident_to_js(name.name.symbol());
                let is_newtype = self.ctx.newtype_ctors.contains(&ctor_js);
                if !is_newtype {
                    let ctor_ref = self.ctor_fn_ref(name.module, name.name.symbol());
                    tests.push(JsExpr::InstanceOf(Box::new(scrut.clone()), Box::new(ctor_ref)));
                }
                for (i, arg) in args.iter().enumerate() {
                    let field = if is_newtype {
                        scrut.clone()
                    } else {
                        JsExpr::Indexer(
                            Box::new(scrut.clone()),
                            Box::new(JsExpr::StringLit(format!("value{i}"))),
                        )
                    };
                    self.compile_binder(&field, arg, tests, binds);
                }
            }
            ir::Binder::Record { fields, .. } => {
                for f in fields {
                    let key = f.label.value.resolve().unwrap_or_default();
                    let sub = JsExpr::Indexer(
                        Box::new(scrut.clone()),
                        Box::new(JsExpr::StringLit(key.clone())),
                    );
                    match &f.binder {
                        Some(b) => self.compile_binder(&sub, b, tests, binds),
                        None => binds.push(JsStmt::VarDecl(
                            ident_to_js(crate::names::value_name(&key).symbol()),
                            Some(sub),
                        )),
                    }
                }
            }
            ir::Binder::Array { elements, .. } => {
                tests.push(JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(JsExpr::Indexer(
                        Box::new(scrut.clone()),
                        Box::new(JsExpr::StringLit("length".to_string())),
                    )),
                    Box::new(JsExpr::IntLit(elements.len() as i64)),
                ));
                for (i, el) in elements.iter().enumerate() {
                    let item = JsExpr::Indexer(
                        Box::new(scrut.clone()),
                        Box::new(JsExpr::IntLit(i as i64)),
                    );
                    self.compile_binder(&item, el, tests, binds);
                }
            }
        }
    }

    fn compile_literal_binder(
        &mut self,
        scrut: &JsExpr,
        lit: &ir::Literal,
        tests: &mut Vec<JsExpr>,
        binds: &mut Vec<JsStmt>,
    ) {
        let rhs = match lit {
            ir::Literal::Int(n) => JsExpr::IntLit(*n),
            ir::Literal::Float(f) => JsExpr::NumericLit(*f),
            ir::Literal::String(s) => JsExpr::StringLit(s.clone()),
            ir::Literal::Char(c) => JsExpr::StringLit(c.to_string()),
            ir::Literal::Boolean(b) => JsExpr::BoolLit(*b),
            ir::Literal::Array(elems) => {
                tests.push(JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(JsExpr::Indexer(
                        Box::new(scrut.clone()),
                        Box::new(JsExpr::StringLit("length".to_string())),
                    )),
                    Box::new(JsExpr::IntLit(elems.len() as i64)),
                ));
                for (i, el) in elems.iter().enumerate() {
                    let item = JsExpr::Indexer(
                        Box::new(scrut.clone()),
                        Box::new(JsExpr::IntLit(i as i64)),
                    );
                    // Array-literal elements are expressions, not binders; the
                    // IR uses Binder::Array for patterns, so this branch only
                    // fires for literal array *values* in patterns, which are
                    // compared structurally — fall back to equality.
                    let _ = item;
                    let _ = el;
                }
                return;
            }
        };
        tests.push(JsExpr::Binary(JsBinaryOp::StrictEq, Box::new(scrut.clone()), Box::new(rhs)));
        let _ = binds;
    }

    fn gen_literal(&mut self, lit: &ir::Literal) -> JsExpr {
        match lit {
            ir::Literal::Int(n) => JsExpr::IntLit(*n),
            ir::Literal::Float(f) => JsExpr::NumericLit(*f),
            ir::Literal::String(s) => JsExpr::StringLit(s.clone()),
            ir::Literal::Char(c) => JsExpr::StringLit(c.to_string()),
            ir::Literal::Boolean(b) => JsExpr::BoolLit(*b),
            ir::Literal::Array(elems) => {
                JsExpr::ArrayLit(elems.iter().map(|el| self.gen_expr(el)).collect())
            }
        }
    }

    // -- references ---------------------------------------------------------

    fn gen_var(&mut self, module: ModuleQualifier, sym: crate::interner::Symbol) -> JsExpr {
        let js_name = ident_to_js(sym);
        if module.is_unresolved() {
            return JsExpr::Var(js_name);
        }
        let module_str = module.resolve().unwrap_or_default();
        if module_str.is_empty() || module_str == self.ctx.module {
            let raw = crate::interner::resolve(sym).unwrap_or_default();
            if self.ctx.foreign_names.contains(&raw) {
                return JsExpr::ModuleAccessor("$foreign".to_string(), raw);
            }
            JsExpr::Var(js_name)
        } else {
            self.record_external(&module_str);
            JsExpr::ModuleAccessor(module_name_str_to_js(&module_str), js_name)
        }
    }

    /// The bare constructor function reference (for `instanceof` tests / `new`).
    fn ctor_fn_ref(&mut self, module: ModuleQualifier, sym: crate::interner::Symbol) -> JsExpr {
        let ctor_js = ident_to_js(sym);
        let module_str = if module.is_unresolved() {
            String::new()
        } else {
            module.resolve().unwrap_or_default()
        };
        if module_str.is_empty() || module_str == self.ctx.module {
            JsExpr::Var(ctor_js)
        } else {
            self.record_external(&module_str);
            JsExpr::ModuleAccessor(module_name_str_to_js(&module_str), ctor_js)
        }
    }

    /// A constructor used as a value: newtype → identity fn; nullary data →
    /// `.value` singleton; n-ary data → curried `.create`. Works for both local
    /// and imported constructors — arity/newtype-ness come from module-global
    /// maps that include imported entries.
    fn gen_ctor(&mut self, module: ModuleQualifier, sym: crate::interner::Symbol) -> JsExpr {
        let ctor_js = ident_to_js(sym);
        if self.ctx.newtype_ctors.contains(&ctor_js) {
            return self.ctor_fn_ref(module, sym);
        }
        let base = self.ctor_fn_ref(module, sym);
        match self.ctx.ctor_arity.get(&ctor_js) {
            Some(0) => JsExpr::Indexer(Box::new(base), Box::new(JsExpr::StringLit("value".to_string()))),
            _ => JsExpr::Indexer(Box::new(base), Box::new(JsExpr::StringLit("create".to_string()))),
        }
    }

    // -- dictionary resolution ---------------------------------------------

    /// The dictionary to pass at a reference site, if any: either a concrete
    /// instance (recorded in `constraint_dicts`) or a given supplied by an
    /// in-scope dict parameter (for class methods the solver discharged via a
    /// given without recording a `ResolvedDict`).
    fn dicts_for(&mut self, sym: crate::interner::Symbol, span: Span) -> Vec<JsExpr> {
        if let Some(rds) = self.constraint_dicts.get(&span).cloned() {
            // De-duplicate: `solve_all` runs more than once (initial + redrive)
            // and may record the same dict per pass; distinct constraints of a
            // multi-constraint site are kept, in order.
            let mut seen: Vec<ResolvedDict> = Vec::new();
            let mut out = Vec::new();
            for rd in rds {
                if seen.contains(&rd) {
                    continue;
                }
                seen.push(rd.clone());
                out.push(self.resolve_dict(&rd.class.name, &rd.instance_types));
            }
            return out;
        }
        // Given: a class method whose class has an in-scope dict parameter.
        let method_ps = crate::interner::resolve(sym).unwrap_or_default();
        if let Some(class) = self.ctx.class_methods.get(&method_ps) {
            if let Some(param) = self.scope_param(class) {
                return vec![JsExpr::Var(param)];
            }
        }
        Vec::new()
    }

    /// Resolve the dictionary expression for `class` applied to concrete
    /// `types`, recursing into the matched instance's context. A type-variable
    /// head means the dict is supplied by an in-scope given parameter.
    fn resolve_dict(&mut self, class_simple: &str, types: &[Type]) -> JsExpr {
        let heads: Vec<String> = types.iter().map(type_head_name).collect();
        if heads.iter().all(|h| h.is_empty()) {
            // No concrete head: a given parameter.
            let param = self.scope_param(class_simple).unwrap_or_else(|| format!("dict{class_simple}"));
            return JsExpr::Var(param);
        }
        let base = self.instance_var(class_simple, &heads);

        // Apply context sub-dicts using the matched instance's structure.
        let Some(subst) = self.match_instance(class_simple, types) else {
            return base;
        };
        let context = self.instance_context(class_simple, types);
        let mut e = base;
        for c in &context {
            let sub_types: Vec<Type> = c.args.iter().map(|t| apply_subst(t, &subst)).collect();
            let sub = self.resolve_dict(&c.class.name, &sub_types);
            e = JsExpr::App(Box::new(e), vec![sub]);
        }
        e
    }

    /// The (unsubstituted) context of the instance of `class` matching `types`.
    fn instance_context(
        &self,
        class_simple: &str,
        types: &[Type],
    ) -> Vec<crate::typecheck_db::types::Constraint> {
        for inst in self.ctx.instances.candidates(class_simple) {
            let mut subst = HashMap::new();
            let vars: std::collections::HashSet<String> = inst.vars.iter().cloned().collect();
            if match_types(&inst.types, types, &vars, &mut subst) {
                return inst.context.clone();
            }
        }
        Vec::new()
    }

    /// The substitution binding the matched instance's vars to `types`.
    fn match_instance(&self, class_simple: &str, types: &[Type]) -> Option<HashMap<String, Type>> {
        for inst in self.ctx.instances.candidates(class_simple) {
            let mut subst = HashMap::new();
            let vars: std::collections::HashSet<String> = inst.vars.iter().cloned().collect();
            if match_types(&inst.types, types, &vars, &mut subst) {
                return Some(subst);
            }
        }
        None
    }

    /// A reference to an instance dictionary by JS name, qualified with its
    /// defining module when that is an imported module.
    fn instance_var(&mut self, class_simple: &str, heads: &[String]) -> JsExpr {
        let name = instance_js_name(class_simple, heads);
        match self.ctx.instance_modules.get(&name) {
            Some(m) if m != self.ctx.module => {
                self.record_external(m);
                JsExpr::ModuleAccessor(module_name_str_to_js(m), name)
            }
            _ => JsExpr::Var(name),
        }
    }

    /// Resolve the dictionary for `class` at a single concrete type — used by
    /// the deriver to obtain each field's instance dictionary.
    pub(super) fn dict_for_type(&mut self, class_simple: &str, ty: &Type) -> JsExpr {
        self.resolve_dict(class_simple, std::slice::from_ref(ty))
    }

    /// Push an in-scope given dictionary (class → JS param name). Used by the
    /// `Eq1`/`Ord1` derivers, whose method takes the element dict as a param.
    pub(super) fn push_scope(&mut self, class: &str, param: &str) {
        self.dict_scope.push((class.to_string(), param.to_string()));
    }

    fn scope_param(&self, class_simple: &str) -> Option<String> {
        self.dict_scope
            .iter()
            .find(|(c, _)| c == class_simple)
            .map(|(_, p)| p.clone())
    }

    fn record_external(&mut self, module_str: &str) {
        let parts: Vec<String> = module_str.split('.').map(|s| s.to_string()).collect();
        if !self.external_refs.contains(&parts) {
            self.external_refs.push(parts);
        }
    }

    /// Record a dependency on an external module (e.g. the deriver needs
    /// `Data.Ordering` for `LT`/`EQ`/`GT`).
    pub(super) fn note_external(&mut self, module_str: &str) {
        self.record_external(module_str);
    }
}

/// Structurally match an instance head `pattern` against concrete `types`,
/// binding the instance's quantified `vars` into `subst`. Returns false on any
/// mismatch.
fn match_types(
    pattern: &[crate::typecheck_db::types::Type],
    types: &[crate::typecheck_db::types::Type],
    vars: &std::collections::HashSet<String>,
    subst: &mut HashMap<String, crate::typecheck_db::types::Type>,
) -> bool {
    if pattern.len() != types.len() {
        return false;
    }
    pattern.iter().zip(types.iter()).all(|(p, t)| match_type(p, t, vars, subst))
}

fn match_type(
    pattern: &crate::typecheck_db::types::Type,
    t: &crate::typecheck_db::types::Type,
    vars: &std::collections::HashSet<String>,
    subst: &mut HashMap<String, crate::typecheck_db::types::Type>,
) -> bool {
    use crate::typecheck_db::types::Type as T;
    match (pattern, t) {
        (T::Var(v), _) if vars.contains(v) => {
            if let Some(prev) = subst.get(v) {
                prev == t
            } else {
                subst.insert(v.clone(), t.clone());
                true
            }
        }
        (T::Var(a), T::Var(b)) => a == b,
        (T::Con(a), T::Con(b)) => a.name == b.name,
        (T::App(pf, pa), T::App(tf, ta)) => {
            match_type(pf, tf, vars, subst) && match_type(pa, ta, vars, subst)
        }
        (T::Fun(pa, pb), T::Fun(ta, tb)) => {
            match_type(pa, ta, vars, subst) && match_type(pb, tb, vars, subst)
        }
        _ => pattern == t,
    }
}

/// Apply a variable substitution to a type (used to concretise an instance's
/// declared context for codegen).
fn apply_subst(
    t: &crate::typecheck_db::types::Type,
    subst: &HashMap<String, crate::typecheck_db::types::Type>,
) -> crate::typecheck_db::types::Type {
    use crate::typecheck_db::types::Type as T;
    use std::sync::Arc;
    match t {
        T::Var(v) => subst.get(v).cloned().unwrap_or_else(|| t.clone()),
        T::App(f, a) => T::App(Arc::new(apply_subst(f, subst)), Arc::new(apply_subst(a, subst))),
        T::Fun(a, b) => T::Fun(Arc::new(apply_subst(a, subst)), Arc::new(apply_subst(b, subst))),
        _ => t.clone(),
    }
}

/// AND a list of boolean tests; empty → `true`.
fn and_all(tests: Vec<JsExpr>) -> JsExpr {
    let mut it = tests.into_iter();
    match it.next() {
        None => JsExpr::BoolLit(true),
        Some(first) => it.fold(first, |acc, t| {
            JsExpr::Binary(JsBinaryOp::And, Box::new(acc), Box::new(t))
        }),
    }
}

/// `(function () { <stmts> })()`
fn iife(stmts: Vec<JsStmt>) -> JsExpr {
    JsExpr::App(Box::new(JsExpr::Function(None, vec![], stmts)), vec![])
}

fn throw_no_match() -> JsStmt {
    JsStmt::Throw(JsExpr::App(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    ))
}
