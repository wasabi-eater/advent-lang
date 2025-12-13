#[cfg(test)]
pub mod test;

use fxhash::FxHashMap;
use im_rc::{Vector, vector};
use itertools::{Itertools, iproduct};

use crate::{
    analysis::{errors, types},
    ast::{self, Expr},
    lexer::Token,
    std_lib::std_func_types
};

use super::types::*;
use core::fmt;
use std::{cell::RefCell, fmt::Debug, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub enum Typing {
    Int,
    Float,
    String,
    Bool,
    Unit,
    Var(TyVar),
    List(Rc<Typing>),
    Arrow(Rc<Typing>, Rc<Typing>),
    Comma(Rc<Typing>, Rc<Typing>),
    TmpTyVar(TmpTyVarId),
}
impl Typing {
    pub fn from(ty: &Type, subst: &FxHashMap<TyVar, Typing>) -> Typing {
        match ty {
            Type::Int => Typing::Int,
            Type::Float => Typing::Float,
            Type::Bool => Typing::Bool,
            Type::String => Typing::String,
            Type::Unit => Typing::Unit,
            &Type::Var(var) => match subst.get(&var) {
                Some(typing) => typing.clone(),
                None => Typing::Var(var),
            },
            Type::List(inner) => Typing::List(Rc::new(Typing::from(inner, subst))),
            Type::Arrow(l, r) => {
                let l: Typing = Typing::from(l, subst);
                let r = Typing::from(r, subst);
                Typing::Arrow(Rc::new(l), Rc::new(r))
            }
            Type::Comma(l, r) => {
                let l = Typing::from(l, subst);
                let r = Typing::from(r, subst);
                Typing::Comma(Rc::new(l), Rc::new(r))
            }
        }
    }
    pub fn try_to_type(&self, arena: &mut TmpTyVarArena) -> errors::Result<Type> {
        match self {
            Typing::Int => Ok(Type::Int),
            Typing::Float => Ok(Type::Float),
            Typing::Bool => Ok(Type::Bool),
            Typing::String => Ok(Type::String),
            Typing::Unit => Ok(Type::Unit),
            &Typing::Var(ty_var) => Ok(Type::Var(ty_var)),
            Typing::List(inner) => Ok(Type::List(Rc::new(inner.try_to_type(arena)?))),
            Typing::Arrow(l, r) => Ok(Type::Arrow(
                Rc::new(l.try_to_type(arena)?),
                Rc::new(r.try_to_type(arena)?),
            )),
            Typing::Comma(l, r) => Ok(Type::Comma(
                Rc::new(l.try_to_type(arena)?),
                Rc::new(r.try_to_type(arena)?),
            )),
            &Typing::TmpTyVar(tmp_ty_var_id) => {
                arena.take_or_err(tmp_ty_var_id)?.try_to_type(arena)
            }
        }
    }
    pub fn display_with(&self, arena: &TmpTyVarArena, f: &mut impl fmt::Write) -> fmt::Result {
        match self {
            Typing::Bool => f.write_str("Bool"),
            Typing::Int => f.write_str("Int"),
            Typing::Float => f.write_str("Float"),
            Typing::String => f.write_str("String"),
            Typing::Unit => f.write_str("()"),
            Typing::Var(var) => write!(f, "{var:?}"),
            Typing::Arrow(l, r) => {
                f.write_str("(")?;
                l.display_with(arena, f)?;
                f.write_str(" -> ")?;
                r.display_with(arena, f)?;
                f.write_str(")")
            }
            Typing::Comma(l, r) => {
                f.write_str("(")?;
                l.display_with(arena, f)?;
                f.write_str(", ")?;
                r.display_with(arena, f)?;
                f.write_str(")")
            }
            Typing::List(inner) => {
                f.write_str("[")?;
                inner.display_with(arena, f)?;
                f.write_str("]")
            }
            Typing::TmpTyVar(tmp) => {
                if let Some(tys) = arena.take(*tmp) {
                    for (i, ty) in tys.iter().enumerate() {
                        if i == 0 {
                            ty.display_with(arena, f)?;
                        } else {
                            f.write_str(" | ")?;
                            ty.display_with(arena, f)?;
                        }
                    }
                    Ok(())
                } else {
                    write!(f, "{tmp:?}")
                }
            }
        }
    }
}
impl Debug for Typing {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Typing::Bool => f.write_str("Bool"),
            Typing::Int => f.write_str("Int"),
            Typing::Float => f.write_str("Float"),
            Typing::String => f.write_str("String"),
            Typing::Unit => f.write_str("()"),
            Typing::Var(var) => write!(f, "{var:?}"),
            Typing::Arrow(l, r) => write!(f, "({:?} -> {:?})", l, r),
            Typing::Comma(l, r) => write!(f, "({:?}, {:?})", l, r),
            Typing::List(inner) => write!(f, "[{:?}]", inner),
            Typing::TmpTyVar(tmp) => write!(f, "?{}", tmp.0),
        }
    }
}
#[derive(Clone, Copy, Debug)]
enum TmpTyVar {
    Root { size: usize },
    Ref(TmpTyVarId),
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TmpTyVarId(usize);
impl Debug for TmpTyVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "?{}", self.0)
    }
}
#[derive(Clone)]
pub struct TmpTyVarArena {
    tmp_ty_vars: RefCell<Vec<TmpTyVar>>,
    group_ty: FxHashMap<TmpTyVarId, Vec<Typing>>,
}
impl TmpTyVarArena {
    pub fn new() -> Self {
        Self {
            tmp_ty_vars: RefCell::new(vec![]),
            group_ty: FxHashMap::default(),
        }
    }
    pub fn root(&self, id: TmpTyVarId) -> TmpTyVarId {
        let tmp_ty_var = self.tmp_ty_vars.borrow()[id.0];
        match tmp_ty_var {
            TmpTyVar::Root { .. } => id,
            TmpTyVar::Ref(next) => {
                let root = self.root(next);
                self.tmp_ty_vars.borrow_mut()[id.0] = TmpTyVar::Ref(root);
                root
            }
        }
    }
    pub fn take(&self, id: TmpTyVarId) -> Option<&[Typing]> {
        let root = self.root(id);
        self.group_ty.get(&root).map(|tys| &**tys)
    }
    pub fn take_or_err(&mut self, id: TmpTyVarId) -> errors::Result<Typing> {
        let Some(tys) = self.take(id) else {
            return Err(errors::Error::UnknownType {
                tmp_id: id,
                arena: self.clone(),
            });
        };
        if tys.len() == 1 {
            Ok(tys[0].clone())
        } else {
            Err(errors::Error::AmbigiousOverload {
                tys: tys.iter().map(|pair| pair.clone()).collect(),
                tmp_id: id,
                arena: self.clone(),
            })
        }
    }
    fn alloc_assigned_many(&mut self, typings: Vec<Typing>) -> TmpTyVarId {
        let id = TmpTyVarId(self.tmp_ty_vars.borrow().len());
        self.tmp_ty_vars.get_mut().push(TmpTyVar::Root { size: 1 });
        self.group_ty.insert(id, typings);
        id
    }
    fn alloc_assigned(&mut self, typing: Typing) -> TmpTyVarId {
        self.alloc_assigned_many(vec![typing])
    }
    fn alloc_unassigned(&mut self) -> TmpTyVarId {
        let id = TmpTyVarId(self.tmp_ty_vars.borrow().len());
        self.tmp_ty_vars.get_mut().push(TmpTyVar::Root { size: 1 });
        id
    }
    pub fn is_same_group(&mut self, l: TmpTyVarId, r: TmpTyVarId) -> bool {
        self.root(l) == self.root(r)
    }
    fn merge(&mut self, l: TmpTyVarId, r: TmpTyVarId, new_ty: Option<Vec<Typing>>) {
        let l = self.root(l);
        let r = self.root(r);
        if l == r {
            if let Some(new_ty) = new_ty {
                self.group_ty.insert(l, new_ty);
            }
            return;
        }
        let TmpTyVar::Root { size: l_size } = self.tmp_ty_vars.borrow()[l.0] else {
            panic!("root is expected")
        };
        let TmpTyVar::Root { size: r_size } = self.tmp_ty_vars.borrow()[r.0] else {
            panic!("root is expected")
        };
        if l_size > r_size {
            self.tmp_ty_vars.get_mut()[r.0] = TmpTyVar::Ref(l);
            self.group_ty.remove(&r);
            if let Some(new_ty) = new_ty {
                self.group_ty.insert(l, new_ty);
            }
        } else {
            self.tmp_ty_vars.get_mut()[l.0] = TmpTyVar::Ref(r);
            self.group_ty.remove(&l);
            if let Some(new_ty) = new_ty {
                self.group_ty.insert(r, new_ty);
            }
        }
    }
}

fn unify(
    l: &Typing,
    r: &Typing,
    arena: &mut TmpTyVarArena,
    expr: Rc<Expr>,
) -> errors::Result<Typing> {
    match (l, r) {
        (Typing::Int, Typing::Int)
        | (Typing::Float, Typing::Float)
        | (Typing::Bool, Typing::Bool)
        | (Typing::String, Typing::String)
        | (Typing::Unit, Typing::Unit) => Ok(l.clone()),
        (&Typing::Var(l_var), &Typing::Var(r_var)) if l_var == r_var => Ok(l.clone()),
        (Typing::Arrow(lp, lr), Typing::Arrow(rp, rr)) => {
            unify(rp, lp, arena, expr.clone())?;
            unify(lr, rr, arena, expr)?;
            Ok(Typing::Arrow(Rc::clone(lp), Rc::clone(lr)))
        }
        (Typing::List(l_inner), Typing::List(r_inner)) => {
            unify(l_inner, r_inner, arena, expr)?;
            Ok(Typing::List(Rc::clone(l_inner)))
        }
        (Typing::Comma(ll, lr), Typing::Comma(rl, rr)) => {
            unify(ll, rl, arena, expr.clone())?;
            unify(lr, rr, arena, expr)?;
            Ok(Typing::Comma(Rc::clone(ll), Rc::clone(lr)))
        }
        (&Typing::TmpTyVar(l), &Typing::TmpTyVar(r)) => {
            unify_tmp_var_id(l, r, arena, expr)?;
            Ok(Typing::TmpTyVar(arena.root(l)))
        }
        (&Typing::TmpTyVar(l), r) => {
            unify_tmp_var_id(l, arena.alloc_assigned(r.clone()), arena, expr)?;
            Ok(Typing::TmpTyVar(arena.root(l)))
        }
        (l, &Typing::TmpTyVar(r)) => {
            unify_tmp_var_id(arena.alloc_assigned(l.clone()), r, arena, expr)?;
            Ok(Typing::TmpTyVar(arena.root(r)))
        }
        _ => Err(errors::Error::TypeMismatch {
            expr,
            expected: r.clone(),
            actual: l.clone(),
            arena: arena.clone(),
        }),
    }
}

fn unify_tmp_var_id(
    l: TmpTyVarId,
    r: TmpTyVarId,
    arena: &mut TmpTyVarArena,
    expr: Rc<Expr>,
) -> errors::Result<()> {
    match (arena.take(l), arena.take(r)) {
        (None, r_ty) => {
            let r_ty = r_ty.map(|tys| tys.to_vec());
            arena.merge(l, r, r_ty);
            Ok(())
        }
        (l_ty, None) => {
            let l_ty = l_ty.map(|tys| tys.to_vec());
            arena.merge(l, r, l_ty);
            Ok(())
        }
        (Some(l_ty), Some(r_ty)) => {
            let unified_types = iproduct!(l_ty.to_vec(), r_ty.to_vec())
                .map(|(l_ty, r_ty)| unify(&l_ty, &r_ty, arena, expr.clone()))
                .collect_vec();
            if unified_types.is_empty() {
                panic!()
            }
            if unified_types.iter().all(|res| res.is_err()) {
                return Err(unified_types.into_iter().next().unwrap().unwrap_err());
            }
            let unified_types = unified_types.into_iter().flatten().collect_vec();
            arena.merge(l, r, Some(unified_types));
            Ok(())
        }
    }
}
struct ExprTyping {
    _expr: Rc<Expr>,
    typing: Typing,
}
pub struct InferencePool {
    tmp_var_arena: TmpTyVarArena,
    expr_typing: FxHashMap<ExprRef, ExprTyping>,
    tyvar_arena: id_arena::Arena<TyVarBody>,
    scope: Scope,
    let_type: FxHashMap<ExprRef, VarType>,
    desugared: FxHashMap<ExprRef, Rc<Expr>>,
    std_func_types: FxHashMap<Rc<str>, Vector<TypeScheme>>,
}
#[derive(Default, Clone)]
pub struct Scope {
    vars: im_rc::HashMap<Rc<str>, Vector<VarType>, fxhash::FxBuildHasher>,
}
#[derive(Clone)]
enum VarType {
    Annotated(TypeScheme),
    Unannotated(Typing),
}

impl InferencePool {
    pub fn new() -> Self {
        let mut tyvar_arena = id_arena::Arena::new();
        let std_func_types = std_func_types(&mut tyvar_arena);
        let scope = Scope {
            vars: std_func_types
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        ty.iter().cloned().map(VarType::Annotated).collect(),
                    )
                })
                .collect(),
        };
        Self {
            tmp_var_arena: TmpTyVarArena::new(),
            expr_typing: FxHashMap::default(),
            tyvar_arena,
            scope,
            let_type: FxHashMap::default(),
            desugared: FxHashMap::default(),
            std_func_types,
        }
    }
    pub fn display(&self, ty: Typing) -> String {
        let mut s = String::new();
        ty.display_with(&self.tmp_var_arena, &mut s).unwrap();
        s
    }
    fn embody(&mut self, type_scheme: &TypeScheme) -> Typing {
        let subst = type_scheme
            .bound_vars
            .iter()
            .copied()
            .map(|var| (var, Typing::TmpTyVar(self.tmp_var_arena.alloc_unassigned())))
            .collect();
        Typing::from(&type_scheme.ty, &subst)
    }
    pub fn infer(&mut self, expr: Rc<Expr>) -> errors::Result<Typing> {
        if let Some(expr_typing) = self.expr_typing.get(&ExprRef(expr.clone())) {
            return Ok(expr_typing.typing.clone());
        }
        let typing = self.infer_inner(expr.clone())?;
        self.expr_typing.insert(
            ExprRef(expr.clone()),
            ExprTyping {
                _expr: expr,
                typing: typing.clone(),
            },
        );
        Ok(typing)
    }
    pub fn infer_inner(&mut self, expr: Rc<Expr>) -> errors::Result<Typing> {
        match &*expr {
            Expr::LitInt(_) => Ok(Typing::Int),
            Expr::LitFloat(_) => Ok(Typing::Float),
            Expr::LitStr(_) => Ok(Typing::String),
            Expr::Unit => Ok(Typing::Unit),
            Expr::LitList(items) => {
                let inner_id = self.tmp_var_arena.alloc_unassigned();
                for item in items {
                    let item_ty = self.infer(item.clone())?;
                    unify(
                        &item_ty,
                        &Typing::TmpTyVar(inner_id),
                        &mut self.tmp_var_arena,
                        item.clone(),
                    )?;
                }
                Ok(Typing::List(Typing::TmpTyVar(inner_id).into()))
            }
            Expr::Brace(statements) if statements.is_empty() => Ok(Typing::Unit),
            Expr::Brace(statements) => {
                let mut scope = self.scope.clone();
                std::mem::swap(&mut scope, &mut self.scope);
                for statement in &statements[..statements.len() - 1] {
                    self.infer(statement.clone())?;
                }
                let last_ty = self.infer(statements[statements.len() - 1].clone())?;
                std::mem::swap(&mut scope, &mut self.scope);
                Ok(last_ty)
            }
            Expr::AppFun(f, param) => {
                let f_ty = self.infer(f.clone())?;
                let param_ty = self.infer(param.clone())?;
                let tmp_id = self.tmp_var_arena.alloc_unassigned();
                unify(
                    &f_ty,
                    &Typing::Arrow(param_ty.into(), Typing::TmpTyVar(tmp_id).into()),
                    &mut self.tmp_var_arena,
                    expr,
                )?;
                Ok(Typing::TmpTyVar(tmp_id).into())
            }
            Expr::BinOp(l, op, r) => {
                let op_ident = Rc::new(Expr::Ident(op.binop_to_str().into()));
                let app_fun = Rc::new(Expr::AppFun(op_ident, l.clone()));
                let app_fun2 = Rc::new(Expr::AppFun(app_fun, r.clone()));
                self.desugared.insert(ExprRef(expr), app_fun2.clone());
                self.infer(app_fun2)
            }
            Expr::UnOp(op, operand) => {
                if *op == Token::Apostrophe {
                    let operand_ty = self.infer(operand.clone())?;
                    Ok(Typing::Arrow(Typing::Unit.into(), operand_ty.into()))
                } else {
                    let op_ident = Rc::new(Expr::Ident(op.binop_to_str().into()));
                    let app_fun = Rc::new(Expr::AppFun(op_ident, operand.clone()));
                    self.desugared.insert(ExprRef(expr), app_fun.clone());
                    self.infer(app_fun)
                }
            }
            Expr::Member(_, _) => todo!(),
            Expr::Ident(name) => {
                let Some(var_ty) = self.scope.vars.get(&*name) else {
                    return Err(errors::Error::UndefiedIdent(name.clone()));
                };
                assert!(var_ty.len() >= 1);
                if var_ty.len() == 1 {
                    match var_ty[0].clone() {
                        VarType::Annotated(type_scheme) => Ok(self.embody(&type_scheme)),
                        VarType::Unannotated(typing) => Ok(typing.clone()),
                    }
                } else {
                    let type_schemes = var_ty
                        .clone()
                        .into_iter()
                        .map(|var_ty| match var_ty {
                            VarType::Annotated(annotated) => annotated.clone(),
                            VarType::Unannotated(_) => unreachable!(),
                        })
                        .collect_vec();
                    let typings = type_schemes
                        .into_iter()
                        .map(|type_scheme| self.embody(&type_scheme))
                        .collect_vec();
                    Ok(Typing::TmpTyVar(
                        self.tmp_var_arena.alloc_assigned_many(typings),
                    ))
                }
            }
            Expr::Let(name, right_expr, None) => {
                let right_ty = self.infer(right_expr.clone())?;
                let var_ty = VarType::Unannotated(right_ty);
                self.scope
                    .vars
                    .insert(name.clone(), vector![var_ty.clone()]);
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
            Expr::Let(name, right_expr, Some(kind_like)) => {
                let assigned_typing = self.infer(right_expr.clone())?;
                let type_scheme: TypeScheme = self.eval_kindlike(kind_like)?;
                let ty = Typing::from(&type_scheme.ty, &FxHashMap::default());
                unify(&assigned_typing, &ty, &mut self.tmp_var_arena, expr.clone())?;
                let var_ty = VarType::Annotated(type_scheme);
                self.scope
                    .vars
                    .insert(name.clone(), vector![var_ty.clone()]);
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
        }
    }
    fn eval_kindlike(&mut self, kind_like: &ast::KindLike) -> errors::Result<TypeScheme> {
        let name_tyvar_map: FxHashMap<Rc<str>, TyVar> = kind_like
            .bound_vars
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    self.tyvar_arena.alloc(TyVarBody {
                        name: Some(name.to_string()),
                    }),
                )
            })
            .collect();
        let mut name_ty_map: FxHashMap<Rc<str>, Type> = name_tyvar_map
            .clone()
            .into_iter()
            .map(|(name, ty_var)| (name, Type::Var(ty_var)))
            .collect();
        name_ty_map.insert("Int".into(), Type::Int);
        name_ty_map.insert("String".into(), Type::String);
        name_ty_map.insert("Float".into(), Type::Float);
        name_ty_map.insert("Bool".into(), Type::Bool);
        let ty = self.eval_kind(&*kind_like.kind, &name_ty_map)?;
        Ok(TypeScheme {
            bound_vars: name_tyvar_map.into_values().collect(),
            ty: Rc::new(ty),
        })
    }
    fn eval_kind(
        &mut self,
        kind: &ast::Kind,
        name_ty_map: &FxHashMap<Rc<str>, Type>,
    ) -> errors::Result<Type> {
        match kind {
            ast::Kind::App(_, _) => todo!(),
            ast::Kind::Arrow(l, r) => Ok(Type::Arrow(
                Rc::new(self.eval_kind(&*l, name_ty_map)?),
                Rc::new(self.eval_kind(&*r, name_ty_map)?),
            )),
            ast::Kind::Comma(l, r) => Ok(Type::Comma(
                Rc::new(self.eval_kind(&*l, name_ty_map)?),
                Rc::new(self.eval_kind(&*r, name_ty_map)?),
            )),
            ast::Kind::Ident(name) => name_ty_map
                .get(&*name)
                .cloned()
                .ok_or_else(|| errors::Error::UndefiedIdent(name.clone())),
            ast::Kind::Unit => Ok(Type::Unit),
            ast::Kind::List(inner) => {
                Ok(Type::List(Rc::new(self.eval_kind(&*inner, name_ty_map)?)))
            }
        }
    }
    pub fn create_program_data(mut self, expr: Rc<Expr>) -> errors::Result<ProgramData> {
        self.infer(expr.clone())?;
        let expr_ty = self
            .expr_typing
            .iter()
            .map(|(expr_ref, expr_typing)| {
                Ok((
                    expr_ref.clone(),
                    Rc::new(
                        expr_typing
                            .typing
                            .clone()
                            .try_to_type(&mut self.tmp_var_arena)?,
                    ),
                ))
            })
            .collect::<errors::Result<FxHashMap<ExprRef, Rc<Type>>>>()?;
        let mut expr_var_id = FxHashMap::default();
        let mut var_arena = id_arena::Arena::new();
        let mut new_scope = self
            .std_func_types
            .iter()
            .map(|(name, tys)| {
                (
                    name.clone(),
                    tys.iter()
                        .cloned()
                        .map(|ty| {
                            var_arena.alloc(types::VarData {
                                name: name.clone(),
                                ty,
                            })
                        })
                        .collect(),
                )
            })
            .collect();
        self.set_expr_var_id(expr, &mut expr_var_id, &mut new_scope, &mut var_arena)?;
        Ok(ProgramData {
            tyvar_arena: self.tyvar_arena,
            var_arena: var_arena,
            expr_ty,
            expr_var_id,
            desugaered: self.desugared,
        })
    }
    fn set_expr_var_id(
        &mut self,
        expr: Rc<Expr>,
        expr_var_id: &mut FxHashMap<ExprRef, types::VarId>,
        new_scope: &mut im_rc::HashMap<Rc<str>, Vector<types::VarId>, fxhash::FxBuildHasher>,
        var_arena: &mut id_arena::Arena<types::VarData>,
    ) -> errors::Result<()> {
        if let Some(desugared) = self.desugared.get(&ExprRef(expr.clone())) {
            return self.set_expr_var_id(desugared.clone(), expr_var_id, new_scope, var_arena);
        }
        match &*expr {
            Expr::LitInt(_) | Expr::LitFloat(_) | Expr::LitStr(_) | Expr::Unit => Ok(()),
            Expr::LitList(items) => {
                for item in items {
                    self.set_expr_var_id(item.clone(), expr_var_id, new_scope, var_arena)?;
                }
                Ok(())
            }
            Expr::BinOp(_, _, _) => unreachable!(),
            Expr::UnOp(Token::Apostrophe, r) => {
                self.set_expr_var_id(r.clone(), expr_var_id, new_scope, var_arena)?;
                Ok(())
            }
            Expr::UnOp(_, _) => unreachable!(),
            Expr::Member(_, _) => todo!(),
            Expr::AppFun(f, p) => {
                self.set_expr_var_id(f.clone(), expr_var_id, new_scope, var_arena)?;
                self.set_expr_var_id(p.clone(), expr_var_id, new_scope, var_arena)?;
                Ok(())
            }
            Expr::Let(name, right_expr, _) => {
                self.set_expr_var_id(right_expr.clone(), expr_var_id, new_scope, var_arena)?;
                let type_scheme = match self.let_type[&ExprRef(expr.clone())].clone() {
                    VarType::Annotated(annotation) => annotation,
                    VarType::Unannotated(typing) => TypeScheme {
                        bound_vars: vector![],
                        ty: Rc::new(typing.try_to_type(&mut self.tmp_var_arena)?),
                    },
                };
                let new_var_id = var_arena.alloc(types::VarData {
                    name: name.clone(),
                    ty: type_scheme,
                });
                expr_var_id.insert(ExprRef(expr.clone()), new_var_id);
                new_scope
                    .entry(name.clone())
                    .or_default()
                    .push_back(new_var_id);
                Ok(())
            }
            Expr::Brace(statements) => {
                let out_scope = new_scope.clone();
                for statement in statements {
                    self.set_expr_var_id(statement.clone(), expr_var_id, new_scope, var_arena)?;
                }
                *new_scope = out_scope;
                Ok(())
            }
            Expr::Ident(name) => {
                let typing = self.expr_typing[&ExprRef(expr.clone())].typing.clone();
                let ty = typing.try_to_type(&mut self.tmp_var_arena)?;
                let matched = new_scope[&*name]
                    .iter()
                    .filter(|&&var_id| var_arena[var_id].ty.assume_subst(&ty).is_some())
                    .collect_vec();
                match matched.len() {
                    0 => Err(errors::Error::UndefiedIdent(name.clone())),
                    1 => {
                        expr_var_id.insert(ExprRef(expr), *matched[0]);
                        Ok(())
                    }
                    2.. => unreachable!(),
                }
            }
        }
    }
}
