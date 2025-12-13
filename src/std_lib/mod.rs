use crate::analysis::types::{TyVarBody, Type, TypeScheme};
use fxhash::FxHashMap;
use id_arena::Arena;
use im_rc::Vector;
use std::rc::Rc;
pub fn def_func(
    name: impl Into<Rc<str>>,
    type_scheme: impl Into<TypeScheme>,
    funcs: &mut FxHashMap<Rc<str>, Vector<TypeScheme>>,
) {
    funcs
        .entry(name.into())
        .or_default()
        .push_back(type_scheme.into());
}
pub fn std_func_types(
    tyvar_arena: &mut Arena<TyVarBody>,
) -> FxHashMap<Rc<str>, Vector<TypeScheme>> {
    let mut funcs = FxHashMap::default();
    def_func("show", Type::arrow(Type::Int, Type::String), &mut funcs);
    def_func("show", Type::arrow(Type::Float, Type::String), &mut funcs);
    def_func("show", Type::arrow(Type::String, Type::String), &mut funcs);
    def_func("show", Type::arrow(Type::Unit, Type::String), &mut funcs);
    def_func("show", Type::arrow(Type::Bool, Type::String), &mut funcs);
    def_func("id", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        TypeScheme::forall(
            [a],
            Type::arrow(Type::Var(a), Type::Var(a)),
        )
    }, &mut funcs);

    def_func("print", Type::arrow(Type::String, Type::Unit), &mut funcs);
    def_func("+", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)), &mut funcs);
    def_func("+", Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)), &mut funcs);
    def_func("+", Type::arrow(Type::String, Type::arrow(Type::String, Type::String)), &mut funcs);
    def_func("+", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        TypeScheme::forall(
            [a],
            Type::arrow(
                Type::list(Type::Var(a)),
                Type::list(Type::Var(a)),
            ),
        )
    }, &mut funcs);
    def_func("-", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)), &mut funcs);
    def_func("-", Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)), &mut funcs);
    def_func("*", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)), &mut funcs);
    def_func("*", Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)), &mut funcs);
    def_func("/", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)), &mut funcs);
    def_func("/", Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)), &mut funcs);
    def_func("==", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Bool)), &mut funcs);
    def_func("==", Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Bool)), &mut funcs);
    def_func("==", Type::arrow(Type::String, Type::arrow(Type::String, Type::Bool)), &mut funcs);
    def_func("==", Type::arrow(Type::Unit, Type::arrow(Type::Unit, Type::Bool)), &mut funcs);
    def_func("==", Type::arrow(Type::Bool, Type::arrow(Type::Bool, Type::Bool)), &mut funcs);

    def_func("-_", Type::arrow(Type::Int, Type::Int), &mut funcs);
    def_func("-_", Type::arrow(Type::Float, Type::Float), &mut funcs);
    def_func("!_", Type::arrow(Type::Bool, Type::Bool), &mut funcs);
    def_func("!_", Type::arrow(Type::Int, Type::Int), &mut funcs);

    
    def_func("&", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)), &mut funcs);
    def_func("&", Type::arrow(Type::Bool, Type::arrow(Type::Bool, Type::Bool)), &mut funcs);

    def_func("|", Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)), &mut funcs);
    def_func("|", Type::arrow(Type::Bool, Type::arrow(Type::Bool, Type::Bool)), &mut funcs);

    def_func(".>", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        let b = tyvar_arena.alloc(TyVarBody::new("b"));
        let c = tyvar_arena.alloc(TyVarBody::new("c"));
        TypeScheme::forall(
            [a, b, c],
            Type::arrow(Type::arrow(Type::Var(a), Type::Var(b)),
                Type::arrow(
                    Type::arrow(Type::Var(b), Type::Var(c)),
                    Type::arrow(Type::Var(a), Type::Var(c))
                )
            )
        )
    }, &mut funcs);

    def_func("<.", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        let b = tyvar_arena.alloc(TyVarBody::new("b"));
        let c = tyvar_arena.alloc(TyVarBody::new("c"));
        TypeScheme::forall(
            [a, b, c],
            Type::arrow(
                Type::arrow(Type::Var(b), Type::Var(c)),
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::Var(b)),
                    Type::arrow(Type::Var(a), Type::Var(c))
                )
            )
        )
    }, &mut funcs);

    def_func("|>", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        let b = tyvar_arena.alloc(TyVarBody::new("b"));
        TypeScheme::forall(
            [a, b],
            Type::arrow(
                Type::Var(a),
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::Var(b)),
                    Type::Var(b)
                )
            )
        )
    }, &mut funcs);

    def_func("<|", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        let b = tyvar_arena.alloc(TyVarBody::new("b"));
        TypeScheme::forall(
            [a, b],
            Type::arrow(
                Type::arrow(Type::Var(a), Type::Var(b)),
                Type::arrow(
                    Type::Var(a),
                    Type::Var(b)
                )
            )
        )
    }, &mut funcs);

    def_func("map", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        let b = tyvar_arena.alloc(TyVarBody::new("b"));
        TypeScheme::forall(
            [a, b],
            Type::arrow(
                Type::arrow(Type::Var(a), Type::Var(b)),
                Type::arrow(
                    Type::list(Type::Var(a)),
                    Type::list(Type::Var(b))
                )
            )
        )
    }, &mut funcs);

    def_func("filter", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        TypeScheme::forall(
            [a],
            Type::arrow(
                Type::arrow(Type::Var(a), Type::Bool),
                Type::arrow(
                    Type::list(Type::Var(a)),
                    Type::list(Type::Var(a))
                )
            )
        )
    }, &mut funcs);

    def_func(",", {
        let a = tyvar_arena.alloc(TyVarBody::new("a"));
        let b = tyvar_arena.alloc(TyVarBody::new("b"));
        TypeScheme::forall(
            [a, b],
            Type::arrow(
                Type::Var(a),
                Type::arrow(
                    Type::Var(b),
                    Type::comma(Type::Var(a), Type::Var(b))
                )
            )
        )
    }, &mut funcs);
    funcs
}
