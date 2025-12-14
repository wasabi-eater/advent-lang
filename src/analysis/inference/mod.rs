#[cfg(test)]
pub mod test;
pub mod typing;

use fxhash::FxHashMap;
use im_rc::{Vector, vector};
use itertools::{Itertools, iproduct};

use super::types::*;
use super::program_data::*;
use crate::{
    analysis::{errors, types},
    ast::{self, Expr},
    lexer::Token,
};
use core::fmt;
use std::{cell::RefCell, fmt::Debug, rc::Rc};
use typing::Typing;

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
    var_arena: id_arena::Arena<VarData>,
    scope: Scope,
    let_type: FxHashMap<ExprRef, VarType>,
    desugared: FxHashMap<ExprRef, Rc<Expr>>,
    extern_funcs: FxHashMap<Rc<str>, Vector<(TypeScheme, VarId)>>,
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
        let tyvar_arena = id_arena::Arena::new();
        let var_arena = id_arena::Arena::new();
        Self {
            tmp_var_arena: TmpTyVarArena::new(),
            expr_typing: FxHashMap::default(),
            tyvar_arena,
            scope: Scope::default(),
            let_type: FxHashMap::default(),
            desugared: FxHashMap::default(),
            var_arena,
            extern_funcs: FxHashMap::default(),
        }
    }
    pub fn extern_func(&mut self, name: impl Into<Rc<str>>, type_scheme: TypeScheme) -> VarId {
        let name = name.into();
        let var_id = self.var_arena.alloc(VarData {
            name: name.clone(),
            ty: type_scheme.clone(),
        });
        self.extern_funcs
            .entry(name.clone())
            .or_default()
            .push_back((type_scheme.clone(), var_id));
        self.scope
            .vars
            .entry(name)
            .or_default()
            .push_back(VarType::Annotated(type_scheme));
        var_id
    }
    pub fn tyvar_arena(&mut self) -> &mut id_arena::Arena<TyVarBody> {
        &mut self.tyvar_arena
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
                    self.infer_as(item.clone(), Typing::TmpTyVar(inner_id))?;
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
                let param_ty = self.infer(param.clone())?;
                let tmp_id = self.tmp_var_arena.alloc_unassigned();
                self.infer_as(
                    f.clone(),
                    Typing::Arrow(param_ty.into(), Typing::TmpTyVar(tmp_id).into()),
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
            Expr::Let(name, assigned_expr, None) => {
                let right_ty = self.infer(assigned_expr.clone())?;
                let var_ty = VarType::Unannotated(right_ty);
                self.scope
                    .vars
                    .insert(name.clone(), vector![var_ty.clone()]);
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
            Expr::Let(name, assigned_expr, Some(kind_like)) => {
                let type_scheme = self.eval_kindlike(kind_like)?;
                let ty = Typing::from(&type_scheme.ty, &FxHashMap::default());
                self.infer_as(assigned_expr.clone(), ty)?;
                let var_ty = VarType::Annotated(type_scheme);
                self.scope
                    .vars
                    .insert(name.clone(), vector![var_ty.clone()]);
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
        }
    }
    pub fn infer_as(&mut self, expr: Rc<Expr>, typing: Typing) -> errors::Result<()> {
        if self.expr_typing.contains_key(&ExprRef(expr.clone())) {
            return Ok(());
        }
        self.infer_as_inner(expr.clone(), &typing)?;
        self.expr_typing.insert(
            ExprRef(expr.clone()),
            ExprTyping {
                _expr: expr,
                typing,
            },
        );
        Ok(())
    }
    pub fn infer_as_inner(&mut self, expr: Rc<Expr>, typing: &Typing) -> errors::Result<()> {
        match &*expr {
            Expr::LitInt(_) => {
                unify(&Typing::Int, typing, &mut self.tmp_var_arena, expr)?;
                Ok(())
            }
            Expr::LitFloat(_) => {
                unify(&Typing::Float, typing, &mut self.tmp_var_arena, expr)?;
                Ok(())
            }
            Expr::LitStr(_) => {
                unify(&Typing::String, typing, &mut self.tmp_var_arena, expr)?;
                Ok(())
            }
            Expr::Unit => unify(&Typing::Unit, typing, &mut self.tmp_var_arena, expr).map(|_| ()),
            Expr::LitList(items) => {
                let inner_id = self.tmp_var_arena.alloc_unassigned();
                unify(
                    &Typing::List(Typing::TmpTyVar(inner_id).into()),
                    typing,
                    &mut self.tmp_var_arena,
                    expr.clone(),
                )?;
                for item in items {
                    self.infer_as(item.clone(), Typing::TmpTyVar(inner_id))?;
                }
                Ok(())
            }
            Expr::Brace(statements) if statements.is_empty() => {
                unify(&Typing::Unit, typing, &mut self.tmp_var_arena, expr)?;
                Ok(())
            }
            Expr::Brace(statements) => {
                let mut scope = self.scope.clone();
                std::mem::swap(&mut scope, &mut self.scope);
                for statement in &statements[..statements.len() - 1] {
                    self.infer(statement.clone())?;
                }
                self.infer_as(statements[statements.len() - 1].clone(), typing.clone())?;
                std::mem::swap(&mut scope, &mut self.scope);
                Ok(())
            }
            Expr::AppFun(f, param) => {
                let param_ty = self.infer(param.clone())?;
                self.infer_as(
                    f.clone(),
                    Typing::Arrow(param_ty.into(), typing.clone().into()),
                )?;
                Ok(())
            }
            Expr::BinOp(l, op, r) => {
                let op_ident = Rc::new(Expr::Ident(op.binop_to_str().into()));
                let app_fun = Rc::new(Expr::AppFun(op_ident, l.clone()));
                let app_fun2 = Rc::new(Expr::AppFun(app_fun, r.clone()));
                self.desugared.insert(ExprRef(expr), app_fun2.clone());
                self.infer_as(app_fun2, typing.clone())
            }
            Expr::UnOp(op, operand) => {
                if *op == Token::Apostrophe {
                    let tmp_var_id = self.tmp_var_arena.alloc_unassigned();
                    unify(
                        &Typing::Arrow(Typing::Unit.into(), Typing::TmpTyVar(tmp_var_id).into()),
                        typing,
                        &mut self.tmp_var_arena,
                        expr.clone(),
                    )?;
                    self.infer_as(operand.clone(), Typing::TmpTyVar(tmp_var_id))?;
                    Ok(())
                } else {
                    let op_ident = Rc::new(Expr::Ident(op.binop_to_str().into()));
                    let app_fun = Rc::new(Expr::AppFun(op_ident, operand.clone()));
                    self.desugared.insert(ExprRef(expr), app_fun.clone());
                    self.infer_as(app_fun, typing.clone())
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
                        VarType::Annotated(type_scheme) => {
                            let ty = self.embody(&type_scheme);
                            unify(&ty, typing, &mut self.tmp_var_arena, expr)?;
                        }
                        VarType::Unannotated(var_typing) => {
                            unify(&var_typing, typing, &mut self.tmp_var_arena, expr)?;
                        }
                    }
                    Ok(())
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
                    let tmp_var_id = self.tmp_var_arena.alloc_assigned_many(typings);
                    unify(
                        &Typing::TmpTyVar(tmp_var_id),
                        typing,
                        &mut self.tmp_var_arena,
                        expr,
                    )?;
                    Ok(())
                }
            }
            Expr::Let(name, assigned_expr, None) => {
                let right_ty = self.infer(assigned_expr.clone())?;
                let var_ty = VarType::Unannotated(right_ty);
                self.scope
                    .vars
                    .insert(name.clone(), vector![var_ty.clone()]);
                self.let_type.insert(ExprRef(expr.clone()), var_ty);
                unify(&Typing::Unit, typing, &mut self.tmp_var_arena, expr.clone())?;
                Ok(())
            }
            Expr::Let(name, assigned_expr, Some(kind_like)) => {
                let type_scheme = self.eval_kindlike(kind_like)?;
                let ty = Typing::from(&type_scheme.ty, &FxHashMap::default());
                self.infer_as(assigned_expr.clone(), ty)?;
                let var_ty = VarType::Annotated(type_scheme);
                self.scope
                    .vars
                    .insert(name.clone(), vector![var_ty.clone()]);
                self.let_type.insert(ExprRef(expr.clone()), var_ty);
                unify(&Typing::Unit, typing, &mut self.tmp_var_arena, expr.clone())?;
                Ok(())
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
        let mut new_scope = self
            .extern_funcs
            .iter()
            .map(|(name, tys)| {
                (
                    name.clone(),
                    tys.iter().cloned().map(|(_, var_id)| var_id).collect(),
                )
            })
            .collect();
        self.set_expr_var_id(expr, &mut expr_var_id, &mut new_scope)?;
        Ok(ProgramData {
            tyvar_arena: self.tyvar_arena,
            var_arena: self.var_arena,
            expr_ty,
            expr_var_id,
            desugaered: self.desugared,
            extern_funcs: self.extern_funcs,
        })
    }
    fn set_expr_var_id(
        &mut self,
        expr: Rc<Expr>,
        expr_var_id: &mut FxHashMap<ExprRef, VarId>,
        new_scope: &mut im_rc::HashMap<Rc<str>, Vector<VarId>, fxhash::FxBuildHasher>,
    ) -> errors::Result<()> {
        if let Some(desugared) = self.desugared.get(&ExprRef(expr.clone())) {
            return self.set_expr_var_id(desugared.clone(), expr_var_id, new_scope);
        }
        match &*expr {
            Expr::LitInt(_) | Expr::LitFloat(_) | Expr::LitStr(_) | Expr::Unit => Ok(()),
            Expr::LitList(items) => {
                for item in items {
                    self.set_expr_var_id(item.clone(), expr_var_id, new_scope)?;
                }
                Ok(())
            }
            Expr::BinOp(_, _, _) => unreachable!(),
            Expr::UnOp(Token::Apostrophe, r) => {
                self.set_expr_var_id(r.clone(), expr_var_id, new_scope)?;
                Ok(())
            }
            Expr::UnOp(_, _) => unreachable!(),
            Expr::Member(_, _) => todo!(),
            Expr::AppFun(f, p) => {
                self.set_expr_var_id(f.clone(), expr_var_id, new_scope)?;
                self.set_expr_var_id(p.clone(), expr_var_id, new_scope)?;
                Ok(())
            }
            Expr::Let(name, right_expr, _) => {
                self.set_expr_var_id(right_expr.clone(), expr_var_id, new_scope)?;
                let type_scheme = match self.let_type[&ExprRef(expr.clone())].clone() {
                    VarType::Annotated(annotation) => annotation,
                    VarType::Unannotated(typing) => TypeScheme {
                        bound_vars: vector![],
                        ty: Rc::new(typing.try_to_type(&mut self.tmp_var_arena)?),
                    },
                };
                let new_var_id = self.var_arena.alloc(VarData {
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
                    self.set_expr_var_id(statement.clone(), expr_var_id, new_scope)?;
                }
                *new_scope = out_scope;
                Ok(())
            }
            Expr::Ident(name) => {
                let typing = self.expr_typing[&ExprRef(expr.clone())].typing.clone();
                let ty = typing.try_to_type(&mut self.tmp_var_arena)?;
                let matched = new_scope[&*name]
                    .iter()
                    .filter(|&&var_id| self.var_arena[var_id].ty.assume_subst(&ty).is_some())
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
