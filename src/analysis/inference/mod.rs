#[cfg(test)]
pub mod test;
pub mod typing;

use fxhash::FxHashMap;
use im_rc::{Vector, vector};
use itertools::Itertools;

use super::program_data::*;
use super::types::*;
use crate::{
    analysis::errors,
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
    group_ty: FxHashMap<TmpTyVarId, Typing>,
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
    pub fn take(&self, id: TmpTyVarId) -> Option<&Typing> {
        let root = self.root(id);
        self.group_ty.get(&root)
    }
    pub fn take_or_err(&mut self, id: TmpTyVarId) -> errors::Result<Typing> {
        let Some(ty) = self.take(id) else {
            return Err(errors::Error::UnknownType {
                tmp_id: id,
                arena: self.clone(),
            });
        };
        Ok(ty.clone())
    }
    fn alloc_assigned(&mut self, typing: Typing) -> TmpTyVarId {
        let id = TmpTyVarId(self.tmp_ty_vars.borrow().len());
        self.tmp_ty_vars.get_mut().push(TmpTyVar::Root { size: 1 });
        self.group_ty.insert(id, typing);
        id
    }
    fn alloc_unassigned(&mut self) -> TmpTyVarId {
        let id = TmpTyVarId(self.tmp_ty_vars.borrow().len());
        self.tmp_ty_vars.get_mut().push(TmpTyVar::Root { size: 1 });
        id
    }
    pub fn is_same_group(&mut self, l: TmpTyVarId, r: TmpTyVarId) -> bool {
        self.root(l) == self.root(r)
    }
    fn merge(&mut self, l: TmpTyVarId, r: TmpTyVarId, new_ty: Option<Typing>) {
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
            arena.merge(l, r, r_ty.cloned());
            Ok(())
        }
        (l_ty, None) => {
            arena.merge(l, r, l_ty.cloned());
            Ok(())
        }
        (Some(l_ty), Some(r_ty)) => {
            let unified_type = unify(&l_ty.clone(), &r_ty.clone(), arena, expr.clone())?;
            arena.merge(l, r, Some(unified_type));
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
    extern_funcs: FxHashMap<Rc<str>, (TypeScheme, VarId)>,
    type_classes: FxHashMap<Rc<str>, TypeClassRef>,
    method_classes: FxHashMap<Rc<str>, TypeClassRef>,
    instances: FxHashMap<TypeClassRef, Vector<Rc<Instance>>>,
}
#[derive(Default, Clone)]
pub struct Scope {
    vars: im_rc::HashMap<Rc<str>, VarType, fxhash::FxBuildHasher>,
}
#[derive(Clone)]
enum VarType {
    Def(TypeScheme),
    Annotated(Type),
    Unannotated(Typing),
}

struct ProgramDataBuilder {
    expr_ident_ref: FxHashMap<ExprRef, IdentRef>,
    let_var_id: FxHashMap<ExprRef, VarId>,
    new_scope: im_rc::HashMap<Rc<str>, (VarId, TypeScheme), fxhash::FxBuildHasher>,
    instances: im_rc::HashMap<TypeClassRef, Vector<Rc<Instance>>, fxhash::FxBuildHasher>,
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
            type_classes: FxHashMap::default(),
            extern_funcs: FxHashMap::default(),
            method_classes: FxHashMap::default(),
            instances: FxHashMap::default(),
        }
    }
    pub fn extern_type_class(&mut self, type_class: TypeClassRef) {
        for method_name in type_class.0.methods.keys() {
            self.method_classes
                .insert(method_name.clone(), type_class.clone());
        }
        self.type_classes
            .insert(type_class.0.name.clone(), type_class);
    }
    pub fn extern_instance(&mut self, instance: Rc<Instance>) {
        self.instances
            .entry(instance.class.clone())
            .or_default()
            .push_back(instance.clone());
    }
    pub fn extern_func(&mut self, name: impl Into<Rc<str>>, type_scheme: TypeScheme) -> VarId {
        let name = name.into();
        let var_id = self.var_arena.alloc(VarData {
            name: name.clone(),
            ty: type_scheme.clone(),
        });
        self.extern_funcs
            .insert(name.clone(), (type_scheme.clone(), var_id));
        self.scope
            .vars
            .insert(name, VarType::Def(type_scheme));
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
    fn embody_with_subst(
        &mut self,
        type_scheme: &TypeScheme,
        mut subst: FxHashMap<TyVar, Typing>,
    ) -> Typing {
        for var in &type_scheme.bound_vars {
            subst.insert(
                *var,
                Typing::TmpTyVar(self.tmp_var_arena.alloc_unassigned()),
            );
        }
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
                    let inner_ty = self.infer(item.clone())?;
                    unify(
                        &inner_ty,
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
                    f.clone(),
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
                if let Some(var_ty) = self.scope.vars.get(&*name) {
                    match var_ty.clone() {
                        VarType::Def(type_scheme) => Ok(self.embody(&type_scheme)),
                        VarType::Annotated(ty) => Ok(Typing::from(&ty, &FxHashMap::default())),
                        VarType::Unannotated(typing) => Ok(typing.clone()),
                    }
                } else if let Some(class) = self.method_classes.get(&*name) {
                    let mut subst = FxHashMap::default();
                    for bound_var in &class.0.bound_vars {
                        subst.insert(
                            *bound_var,
                            Typing::TmpTyVar(self.tmp_var_arena.alloc_unassigned()),
                        );
                    }
                    let type_scheme = &class.0.methods[&*name].clone();
                    Ok(self.embody_with_subst(&type_scheme, subst))
                } else {
                    Err(errors::Error::UndefiedIdent(name.clone()))
                }
            }
            Expr::Let(name, assigned_expr, None) => {
                let assigned_ty = self.infer(assigned_expr.clone())?;
                let var_ty = VarType::Unannotated(assigned_ty);
                self.scope.vars.insert(name.clone(), var_ty.clone());
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
            Expr::Let(name, assigned_expr, Some(kind)) => {
                let ty = self.eval_kind(kind, &Self::std_defined_type_name())?;
                let assigned_ty = self.infer(assigned_expr.clone())?;
                unify(
                    &assigned_ty,
                    &Typing::from(&ty, &FxHashMap::default()),
                    &mut self.tmp_var_arena,
                    assigned_expr.clone(),
                )?;
                let var_ty = VarType::Annotated(ty);
                self.scope.vars.insert(name.clone(), var_ty.clone());
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
            Expr::Def(name, assigned_expr, kind_like) => {
                let type_scheme = self.eval_kindlike(kind_like)?;
                let ty = Typing::from(&type_scheme.ty, &FxHashMap::default());
                let assigned_ty = self.infer(assigned_expr.clone())?;
                unify(
                    &assigned_ty,
                    &ty,
                    &mut self.tmp_var_arena,
                    assigned_expr.clone(),
                )?;
                let var_ty = VarType::Def(type_scheme);
                self.scope.vars.insert(name.clone(), var_ty.clone());
                self.let_type.insert(ExprRef(expr), var_ty);
                Ok(Typing::Unit)
            }
        }
    }
    fn std_defined_type_name() -> FxHashMap<Rc<str>, Type> {
        FxHashMap::from_iter([
            ("Int".into(), Type::Int),
            ("Float".into(), Type::Float),
            ("String".into(), Type::String),
            ("Bool".into(), Type::Bool)
        ])
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
        name_ty_map.extend(Self::std_defined_type_name());
        let ty = self.eval_kind(&*kind_like.kind, &name_ty_map)?;
        Ok(TypeScheme {
            bound_vars: name_tyvar_map.into_values().collect(),
            ty: Rc::new(ty),
            constraints: Vector::new(),
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
        let new_scope = self
            .extern_funcs
            .iter()
            .map(|(name, (type_scheme, var_id))| (name.clone(), (*var_id, type_scheme.clone())))
            .collect();
        let mut program_data_builder = ProgramDataBuilder {
            expr_ident_ref: FxHashMap::default(),
            let_var_id: FxHashMap::default(),
            new_scope,
            instances: self.instances.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        };
        self.set_program_data(expr, &mut program_data_builder)?;
        Ok(ProgramData {
            tyvar_arena: self.tyvar_arena,
            var_arena: self.var_arena,
            expr_ty,
            expr_ident_ref: program_data_builder.expr_ident_ref,
            let_var_ids: program_data_builder.let_var_id,
            desugaered: self.desugared,
            extern_funcs: self.extern_funcs,
            type_classes: self.type_classes,
            method_classes: self.method_classes,
            instances: self.instances,
        })
    }
    fn set_program_data(
        &mut self,
        expr: Rc<Expr>,
        program_data_builder: &mut ProgramDataBuilder,
    ) -> errors::Result<()> {
        if let Some(desugared) = self.desugared.get(&ExprRef(expr.clone())) {
            return self.set_program_data(desugared.clone(), program_data_builder);
        }
        match &*expr {
            Expr::LitInt(_) | Expr::LitFloat(_) | Expr::LitStr(_) | Expr::Unit => Ok(()),
            Expr::LitList(items) => {
                for item in items {
                    self.set_program_data(item.clone(), program_data_builder)?;
                }
                Ok(())
            }
            Expr::BinOp(_, _, _) => unreachable!(),
            Expr::UnOp(Token::Apostrophe, r) => {
                self.set_program_data(r.clone(), program_data_builder)?;
                Ok(())
            }
            Expr::UnOp(_, _) => unreachable!(),
            Expr::Member(_, _) => todo!(),
            Expr::AppFun(f, p) => {
                self.set_program_data(f.clone(), program_data_builder)?;
                self.set_program_data(p.clone(), program_data_builder)?;
                Ok(())
            }
            Expr::Def(name, assigned_expr, _) => {
                let VarType::Def(type_scheme) = self.let_type[&ExprRef(expr.clone())].clone() else {
                    panic!("unexpected var type");
                };
                let new_var_id = self.var_arena.alloc(VarData {
                    name: name.clone(),
                    ty: type_scheme.clone(),
                });
                let old_instances = program_data_builder.instances.clone();
                for instance in &type_scheme.constraints{
                    program_data_builder
                        .instances
                        .entry(instance.class.clone())
                        .or_default()
                        .push_back(instance.clone());
                }
                self.set_program_data(assigned_expr.clone(), program_data_builder)?;
                program_data_builder.instances = old_instances;

                program_data_builder
                    .let_var_id
                    .insert(ExprRef(expr.clone()), new_var_id);
                program_data_builder
                    .new_scope
                    .insert(name.clone(), (new_var_id, type_scheme));
                Ok(())
            }
            Expr::Let(name, assigned_expr, _) => {
                let ty = match self.let_type[&ExprRef(expr.clone())].clone() {
                    VarType::Def(_) => panic!("unexpeceted"),
                    VarType::Annotated(ty) => ty,
                    VarType::Unannotated(typing) => typing.try_to_type(&mut self.tmp_var_arena)?,
                };
                let type_scheme = TypeScheme::forall([], ty.clone());
                let new_var_id = self.var_arena.alloc(VarData {
                    name: name.clone(),
                    ty: type_scheme.clone(),
                });
                self.set_program_data(assigned_expr.clone(), program_data_builder)?;

                program_data_builder
                    .let_var_id
                    .insert(ExprRef(expr.clone()), new_var_id);
                program_data_builder
                    .new_scope
                    .insert(name.clone(), (new_var_id, type_scheme));
                Ok(())
            }
            Expr::Brace(statements) => {
                let out_scope = program_data_builder.new_scope.clone();
                for statement in statements {
                    self.set_program_data(statement.clone(), program_data_builder)?;
                }
                program_data_builder.new_scope = out_scope;
                Ok(())
            }
            Expr::Ident(name) => {
                let typing = self.expr_typing[&ExprRef(expr.clone())].typing.clone();
                let ty = typing.try_to_type(&mut self.tmp_var_arena)?;
                if let Some((var_id, type_scheme)) = program_data_builder.new_scope.get(&*name) {
                    let subst = type_scheme.assume_subst(&ty).unwrap();
                    let given_instance: im_rc::HashMap<Rc<Instance>, Rc<Instance>, std::hash::BuildHasherDefault<fxhash::FxHasher>> = type_scheme
                        .constraints
                        .iter()
                        .map(|instance| (instance.clone(), Rc::new(instance.subst(&subst))))
                        .collect();
                    if !given_instance.is_empty() {
                        println!("{given_instance:?}");
                    }
                    if let Some(instance) = given_instance.values().find(|&inst| {
                        !program_data_builder
                            .instances
                            .get(&inst.class)
                            .is_some_and(|instances| instances.contains(&inst))
                    }) {
                        return Err(errors::Error::MissingInstance { instance: instance.clone() });
                    }
                    program_data_builder
                        .expr_ident_ref
                        .insert(ExprRef(expr.clone()), IdentRef::Var(*var_id, given_instance));
                    return Ok(());
                }
                let Some(type_class) = self.method_classes.get(&*name) else {
                    return Err(errors::Error::UndefiedIdent(name.clone()));
                };
                let method_type_scheme = type_class.0.methods[&*name].clone();
                let Some(subst) = method_type_scheme.assume_subst(&ty) else {
                    return Err(errors::Error::UndefiedIdent(name.clone()));
                };

                let method_type_scheme = method_type_scheme.subst(&subst);
                let candidates = self.instances[&type_class]
                    .iter()
                    .cloned()
                    .filter(|instance| {
                        instance.method_type_scheme(name)
                            .is_some_and(|method_scheme| {
                                method_scheme
                                    .assume_subst(&ty)
                                    .is_some()
                            })
                    })
                    .collect_vec();
                match candidates.len() {
                    0 => {
                        let expeceted_instance = Instance {
                            class: type_class.clone(),
                            assigned_types: method_type_scheme
                                .bound_vars
                                .iter()
                                .map(|var| subst[var].clone())
                                .collect(),
                        };
                        Err(errors::Error::MissingInstance {
                            instance: Rc::new(expeceted_instance),
                        })
                    },
                    1 => {
                        let candidate = candidates[0].clone();
                        let method_type_scheme = candidate
                            .method_type_scheme(name)
                            .unwrap();
                        let subst = method_type_scheme.assume_subst(&ty).unwrap();
                        let method_constraints: im_rc::HashMap<Rc<Instance>, Rc<Instance>, std::hash::BuildHasherDefault<fxhash::FxHasher>> = method_type_scheme
                            .constraints
                            .iter()
                            .map(|instance| (instance.clone(), Rc::new(instance.subst(&subst))))
                            .collect();
                        if let Some(instance) = method_constraints.values().find(|&inst| {
                        !program_data_builder
                            .instances
                            .get(&inst.class)
                            .is_some_and(|instances| instances.contains(&inst))
                        }) {
                            return Err(errors::Error::MissingInstance { instance: instance.clone() });
                        }
                        program_data_builder.expr_ident_ref.insert(
                            ExprRef(expr.clone()),
                            IdentRef::Method(candidate, name.clone(), method_constraints),
                        );
                        Ok(())
                    }
                    2.. => Err(errors::Error::AmbigiousOverload {
                        name: name.clone(),
                        candidates,
                    }),
                }
            }
        }
    }
}
