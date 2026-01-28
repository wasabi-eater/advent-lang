use super::*;
#[test]
pub fn unify_test() {
    let mut tmp_ty_var_arena = TmpTyVarArena::new();
    let a = tmp_ty_var_arena.alloc_unassigned();
    println!("{:?}", tmp_ty_var_arena.tmp_ty_vars);
    println!("{:?}", tmp_ty_var_arena.group_ty);
    println!("{:?}", tmp_ty_var_arena.root(a));
    println!("{:?}", tmp_ty_var_arena.tmp_ty_vars);
    println!("{:?}", tmp_ty_var_arena.group_ty);
    let int = tmp_ty_var_arena.alloc_assigned(Typing::Int);
    println!("{:?}", tmp_ty_var_arena.tmp_ty_vars);
    println!("{:?}", tmp_ty_var_arena.group_ty);
    unify_tmp_var_id(a, int, &mut tmp_ty_var_arena, Rc::new(Expr::Unit(Span::dummy()))).unwrap();
    println!("{:?}", tmp_ty_var_arena.tmp_ty_vars);
    println!("{:?}", tmp_ty_var_arena.group_ty);
    println!("{:?}", tmp_ty_var_arena.root(a));
    println!("{:?}", tmp_ty_var_arena.root(int));
    println!("{:?}", tmp_ty_var_arena.take(a));
}
