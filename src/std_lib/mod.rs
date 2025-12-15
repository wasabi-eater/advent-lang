use crate::{
    analysis::{
        inference::InferencePool,
        program_data::VarId,
        types::{Instance, TyVarBody, Type, TypeClass, TypeClassRef, TypeScheme},
    },
    runner::{core::Runner, core::Variable, obj::Func, obj::Object},
};
use fxhash::FxHashMap;
use im_rc::{HashMap, vector};

macro_rules! native_func {
    ($runner_ident:ident, $p:pat => $body:expr) => {
        Object::Func(Func::NativeFunc(Rc::new(
            move |$runner_ident: &mut Runner, arg: Rc<Object>| {
                match &*arg {
                    $p => $body,
                    #[allow(unreachable_patterns)]
                    _ => panic!("invalid argument type for native function"),
                }
            },
        )))
    };
}
macro_rules! curry {
    ([$($captured:ident),*], $runner_ident: ident, $p:pat => $body:expr) => {
        native_func!(_runner_ident,
            arg0 => {
                let arg0 = arg0.clone();
                $(let $captured = $captured.clone();)*
                Ok(Rc::new(native_func!($runner_ident,
                    arg1 => {
                        let arg0 = arg0.clone();
                        let arg1 = arg1.clone();
                        match (arg0, arg1) {
                            $p => $body,
                            #[allow(unreachable_patterns)]
                            _ => panic!("invalid argument types for curried native function"),
                        }
                    }
                )))
            }
        )
    };
}

use core::panic;
use std::rc::Rc;
pub struct StdLibDefiner<'a> {
    inference_pool: &'a mut InferencePool,
    funcs: FxHashMap<VarId, (Rc<str>, TypeScheme, Variable)>,
    instance_methods: FxHashMap<Rc<Instance>, FxHashMap<Rc<str>, Variable>>,
}
pub struct StdLib {
    pub extern_funcs: FxHashMap<VarId, (Rc<str>, TypeScheme, Variable)>,
    pub instance_methods: FxHashMap<Rc<Instance>, FxHashMap<Rc<str>, Variable>>,
}
impl<'a> StdLibDefiner<'a> {
    pub fn new(inference_pool: &'a mut InferencePool) -> Self {
        StdLibDefiner {
            inference_pool,
            funcs: FxHashMap::default(),
            instance_methods: FxHashMap::default(),
        }
    }
    fn def_type_class(&mut self, type_class: TypeClassRef) {
        self.inference_pool.extern_type_class(type_class);
    }
    fn def_instance(
        &mut self,
        type_class: TypeClassRef,
        assigned_types: impl IntoIterator<Item = Type>,
        method_bodys: &HashMap<&'static str, impl Into<Variable> + Clone>,
    ) {
        let instance = Rc::new(Instance {
            class: type_class.clone(),
            assigned_types: assigned_types.into_iter().collect(),
        });
        self.inference_pool.extern_instance(instance.clone());
        self.instance_methods.insert(
            instance.clone(),
            FxHashMap::from_iter(type_class.0.methods.keys().map(|method_name| {
                (
                    method_name.clone(),
                    method_bodys
                        .get(&**method_name)
                        .expect("method body not provided")
                        .clone()
                        .into(),
                )
            })),
        );
    }
    fn def_func(
        &mut self,
        name: impl Into<Rc<str>>,
        type_scheme: impl Into<TypeScheme>,
        obj: impl Into<Variable>,
    ) {
        let name = name.into();
        let type_scheme = type_scheme.into();
        let var_id = self
            .inference_pool
            .extern_func(name.clone(), type_scheme.clone());

        self.funcs.insert(var_id, (name, type_scheme, obj.into()));
    }
    fn def_show_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let show_class = TypeClassRef(Rc::new(TypeClass {
            name: "Show".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "show".into(),
                TypeScheme::forall([a], Type::arrow(Type::Var(a), Type::String)),
            )]),
        }));
        self.def_type_class(show_class.clone());

        // Show for Int
        self.def_instance(
            show_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "show",
                Rc::new(native_func!(_runner,
                    Object::Int(n) => {
                        Ok(Rc::new(Object::String(Rc::new(n.to_string()))))
                    }
                )),
            )]),
        );

        //Show for Float
        self.def_instance(
            show_class.clone(),
            [Type::Float],
            &HashMap::from_iter([(
                "show",
                Rc::new(native_func!(_runner,
                    Object::Float(n) => {
                        Ok(Rc::new(Object::String(Rc::new(n.to_string()))))
                    }
                )),
            )]),
        );

        //Show for Bool
        self.def_instance(
            show_class.clone(),
            [Type::Bool],
            &HashMap::from_iter([(
                "show",
                Rc::new(native_func!(_runner,
                    Object::Bool(b) => {
                        Ok(Rc::new(Object::String(Rc::new(b.to_string()))))
                    }
                )),
            )]),
        );

        // Show for String
        self.def_instance(
            show_class.clone(),
            [Type::String],
            &HashMap::from_iter([(
                "show",
                Rc::new(native_func!(_runner,
                    Object::String(s) => {
                        Ok(Rc::new(Object::String(s.clone())))
                    }
                )),
            )]),
        );

        // Show for Unit
        self.def_instance(
            show_class,
            [Type::Unit],
            &HashMap::from_iter([(
                "show",
                Rc::new(native_func!(_runner,
                    Object::Unit => {
                        Ok(Rc::new(Object::String(Rc::new("()".to_string()))))
                    }
                )),
            )]),
        );
    }
    fn def_add_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let add_class = TypeClassRef(Rc::new(TypeClass {
            name: "Add".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "+".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(add_class.clone());

        // Add for Int
        self.def_instance(
            add_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "+",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Int(x + y)))
                    }
                )),
            )]),
        );

        // Add for Float
        self.def_instance(
            add_class.clone(),
            [Type::Float],
            &HashMap::from_iter([(
                "+",
                Rc::new(curry!([], _runner,
                    (Object::Float(x), Object::Float(y)) => {
                        Ok(Rc::new(Object::Float(x + y)))
                    }
                )),
            )]),
        );

        // Add for String
        self.def_instance(
            add_class.clone(),
            [Type::String],
            &HashMap::from_iter([(
                "+",
                Rc::new(curry!([], _runner,
                    (Object::String(x), Object::String(y)) => {
                        let mut result = Rc::unwrap_or_clone(x);
                        result.push_str(&y);
                        Ok(Rc::new(Object::String(Rc::new(result))))
                    }
                )),
            )]),
        );

        // Add for List
        let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("c"));
        self.def_instance(
            add_class,
            [Type::List(Rc::new(Type::Var(b)))],
            &HashMap::from_iter([(
                "+",
                Rc::new(curry!([], _runner,
                    (Object::List(x), Object::List(y)) => {
                        let mut result = x.clone();
                        result.append(y);
                        Ok(Rc::new(Object::List(result)))
                    }
                )),
            )]),
        );
    }
    fn def_sub_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let sub_class = TypeClassRef(Rc::new(TypeClass {
            name: "Sub".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "-".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(sub_class.clone());

        // Sub for Int
        self.def_instance(
            sub_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "-",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => Ok(Rc::new(Object::Int(x - y)))
                )),
            )]),
        );

        // Sub for Float
        self.def_instance(
            sub_class,
            [Type::Float],
            &HashMap::from_iter([(
                "-",
                Rc::new(curry!([], _runner,
                    (Object::Float(x), Object::Float(y)) => Ok(Rc::new(Object::Float(x - y)))
                ))
            )]),
        );
    }
    fn def_mul_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let mul_class = TypeClassRef(Rc::new(TypeClass {
            name: "Mul".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "*".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(mul_class.clone());

        // Mul for Int
        self.def_instance(
            mul_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "*",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Int(x * y)))
                    }
                )),
            )]),
        );
        // Mul for Float
        self.def_instance(
            mul_class,
            [Type::Float],
            &HashMap::from_iter([(
                "*",
                Rc::new(curry!([], _runner,
                    (Object::Float(x), Object::Float(y)) => {
                        Ok(Rc::new(Object::Float(x * y)))
                    }
                )),
            )]),
        );
    }
    fn def_div_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let div_class = TypeClassRef(Rc::new(TypeClass {
            name: "Div".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "/".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(div_class.clone());

        // Div for Int
        self.def_instance(
            div_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "/",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Int(x / y)))
                    }
                )),
            )]),
        );
        // Div for Float
        self.def_instance(
            div_class,
            [Type::Float],
            &HashMap::from_iter([(
                "/",
                Rc::new(curry!([], _runner,
                    (Object::Float(x), Object::Float(y)) => {
                        Ok(Rc::new(Object::Float(x / y)))
                    }
                ))
            )]),
        );
    }
    fn def_mod_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let mod_class = TypeClassRef(Rc::new(TypeClass {
            name: "Mod".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "%".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(mod_class.clone());

        // Mod for Int
        self.def_instance(
            mod_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "%",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Int(x % y)))
                    }
                )),
            )]),
        );
        // Mod for Float
        self.def_instance(
            mod_class,
            [Type::Float],
            &HashMap::from_iter([(
                "%",
                Rc::new(curry!([], _runner,
                    (Object::Float(x), Object::Float(y)) => {
                        Ok(Rc::new(Object::Float(x % y)))
                    }
                )),
            )]),
        );
    }
    fn def_neg_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let neg_class = TypeClassRef(Rc::new(TypeClass {
            name: "Neg".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "-_".into(),
                TypeScheme::forall([a], Type::arrow(Type::Var(a), Type::Var(a))),
            )]),
        }));
        self.def_type_class(neg_class.clone());

        // Neg for Int
        self.def_instance(
            neg_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "-_",
                Rc::new(native_func!(_runner,
                    Object::Int(x) => {
                        Ok(Rc::new(Object::Int(-x)))
                    }
                )),
            )]),
        );
        // Neg for Float
        self.def_instance(
            neg_class,
            [Type::Float],
            &HashMap::from_iter([(
                "-_",
                Rc::new(native_func!(_runner,
                    Object::Float(x) => {
                        Ok(Rc::new(Object::Float(-x)))
                    }
                )),
            )]),
        );
    }
    fn def_not_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let not_class = TypeClassRef(Rc::new(TypeClass {
            name: "Not".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "!_".into(),
                TypeScheme::forall([a], Type::arrow(Type::Var(a), Type::Var(a))),
            )]),
        }));
        self.def_type_class(not_class.clone());

        // Not for Bool
        self.def_instance(
            not_class.clone(),
            [Type::Bool],
            &HashMap::from_iter([(
                "!_",
                Rc::new(native_func!(_runner,
                    Object::Bool(b) => {
                        Ok(Rc::new(Object::Bool(!b)))
                    }
                )),
            )]),
        );
        // Not for Int
        self.def_instance(
            not_class,
            [Type::Int],
            &HashMap::from_iter([(
                "!_",
                Rc::new(native_func!(_runner,
                    Object::Int(x) => {
                        Ok(Rc::new(Object::Int(!x)))
                    }
                )),
            )]),
        );
    }
    fn def_and_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let and_class = TypeClassRef(Rc::new(TypeClass {
            name: "And".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "&".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(and_class.clone());

        // And for Bool
        self.def_instance(
            and_class.clone(),
            [Type::Bool],
            &HashMap::from_iter([(
                "&",
                Rc::new(curry!([], _runner,
                    (Object::Bool(x), Object::Bool(y)) => {
                        Ok(Rc::new(Object::Bool(x & y)))
                    }
                )),
            )]),
        );
        // And for Int
        self.def_instance(
            and_class,
            [Type::Int],
            &HashMap::from_iter([(
                "&",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Int(x & y)))
                    }
                ))
            )]),
        );
    }
    fn def_or_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let or_class = TypeClassRef(Rc::new(TypeClass {
            name: "Or".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "|".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
            )]),
        }));
        self.def_type_class(or_class.clone());

        // Or for Bool
        self.def_instance(
            or_class.clone(),
            [Type::Bool],
            &HashMap::from_iter([(
                "|",
                Rc::new(curry!([], _runner,
                    (Object::Bool(x), Object::Bool(y)) => {
                        Ok(Rc::new(Object::Bool(x | y)))
                    }
                )),
            )]),
        );
        // Or for Int
        self.def_instance(
            or_class,
            [Type::Int],
            &HashMap::from_iter([(
                "|",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Int(x | y)))
                    }
                )),
            )]),
        );
    }
    fn def_eq_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let eq_class = TypeClassRef(Rc::new(TypeClass {
            name: "Eq".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "==".into(),
                TypeScheme::forall(
                    [a],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Bool)),
                ),
            )]),
        }));
        self.def_type_class(eq_class.clone());

        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let constraint = Rc::new(Instance {
            class: eq_class.clone(),
            assigned_types: vector![Type::Var(a)],
        });
        self.def_func(
            "!=",
            TypeScheme::forall_with_constraints(
                [a],
                Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Bool)),
                [constraint.clone()],
            ),
            Variable::Def(Rc::new(move |_, instance_replace| {
                let eq_instance = instance_replace[&constraint.clone()].clone();
                Ok(Rc::new(curry!([eq_instance], runner,
                    (l, r) => {
                        let eq_func = runner.instance_methods[&eq_instance]["=="].clone();
                        let eq_func = runner.read_var(&eq_func, im_rc::HashMap::default())?;
                        let Object::Func(eq_func) = &*eq_func else {
                            panic!("Eq::== is not a Func")
                        };
                        let Object::Func(f) = &*runner.call(eq_func, Rc::new(l))? else {
                            panic!("Eq::== did not return a Func")
                        };
                        let eq_result = runner.call(f, Rc::new(r))?;
                        match &*eq_result {
                            Object::Bool(b) => {
                                Ok(Rc::new(Object::Bool(!b)))
                            },
                            _ => panic!("Eq::== did not return a Bool"),
                        }
                    }
                )))
            })),
        );

        // Eq for Int
        self.def_instance(
            eq_class.clone(),
            [Type::Int],
            &HashMap::from_iter([(
                "==",
                Rc::new(curry!([], _runner,
                    (Object::Int(x), Object::Int(y)) => {
                        Ok(Rc::new(Object::Bool(x == y)))
                    }
                )),
            )]),
        );
        // Eq for Float
        self.def_instance(
            eq_class.clone(),
            [Type::Float],
            &HashMap::from_iter([(
                "==",
                Rc::new(curry!([], _runner,
                    (Object::Float(x), Object::Float(y)) => {
                        Ok(Rc::new(Object::Bool(x == y)))
                    }
                )),
            )]),
        );
        //Eq for Bool
        self.def_instance(
            eq_class.clone(),
            [Type::Bool],
            &HashMap::from_iter([(
                "==",
                Rc::new(curry!([], _runner,
                    (Object::Bool(x), Object::Bool(y)) => {
                        Ok(Rc::new(Object::Bool(x == y)))
                    }
                )),
            )]),
        );
        //Eq for String
        self.def_instance(
            eq_class.clone(),
            [Type::String],
            &HashMap::from_iter([(
                "==",
                Rc::new(curry!([], _runner,
                    (Object::String(x), Object::String(y)) => {
                        Ok(Rc::new(Object::Bool(x == y)))
                    }
                )),
            )]),
        );
        //Eq for Unit
        self.def_instance(
            eq_class,
            [Type::Unit],
            &HashMap::from_iter([(
                "==",
                Rc::new(curry!([], _runner,
                    (Object::Unit, Object::Unit) => {
                        Ok(Rc::new(Object::Bool(true)))
                    }
                )),
            )]),
        );
    }
    fn def_len_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let len_class = TypeClassRef(Rc::new(TypeClass {
            name: "Len".into(),
            bound_vars: vec![a],
            methods: FxHashMap::from_iter([(
                "len".into(),
                TypeScheme::forall([a], Type::arrow(Type::Var(a), Type::Int)),
            )]),
        }));
        self.def_type_class(len_class.clone());

        // Len for String
        self.def_instance(
            len_class.clone(),
            [Type::String],
            &HashMap::from_iter([(
                "len",
                Rc::new(native_func!(_runner,
                    Object::String(s) => {
                        Ok(Rc::new(Object::Int(s.len() as i64)))
                    }
                )),
            )]),
        );
        // Len for List
        let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
        self.def_instance(
            len_class,
            [Type::list(Type::Var(b))],
            &HashMap::from_iter([(
                "len",
                Rc::new(native_func!(_runner,
                    Object::List(elems) => {
                        Ok(Rc::new(Object::Int(elems.len() as i64)))
                    }
                )),
            )]),
        );
    }
    fn def_list_functions(&mut self) {
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::Var(b)),
                    Type::arrow(Type::list(Type::Var(a)), Type::list(Type::Var(b))),
                ),
            )
        };
        self.def_func(
            "map",
            type_scheam,
            native_func!(_runner,
                Object::Func(f) => {
                    let f = f.clone();
                    Ok(Rc::new(native_func!(_runner,
                        Object::List(elems) => {
                            let mut new_elems = im_rc::Vector::new();
                            for elem in elems.iter() {
                                let mapped = _runner.call(&f, elem.clone())?;
                                new_elems.push_back(mapped);
                            }
                            Ok(Rc::new(Object::List(new_elems)))
                        }
                    )))
                }
            ),
        );

        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            TypeScheme::forall(
                [a],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::Bool),
                    Type::arrow(Type::list(Type::Var(a)), Type::list(Type::Var(a))),
                ),
            )
        };
        self.def_func(
            "filter",
            type_scheam,
            native_func!(_runner,
                Object::Func(f) => {
                    let f = f.clone();
                    Ok(Rc::new(native_func!(_runner,
                        Object::List(elems) => {
                            let mut new_elems = im_rc::Vector::new();
                            for elem in elems.iter() {
                                let pred = _runner.call(&f, elem.clone())?;
                                if let Object::Bool(b) = *pred {
                                    if b {
                                        new_elems.push_back(elem.clone());
                                    }
                                } else {
                                    panic!("filter predicate must return a boolean");
                                }
                            }
                            Ok(Rc::new(Object::List(new_elems)))
                        }
                    )))
                }
            ),
        );
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::list(Type::Var(a)),
                    Type::arrow(
                        Type::list(Type::Var(b)),
                        Type::list(Type::comma(Type::Var(a), Type::Var(b))),
                    ),
                ),
            )
        };
        self.def_func("zip", type_scheam,
            curry!([], _runner,
                (Object::List(list1), Object::List(list2)) => {
                    let len = std::cmp::min(list1.len(), list2.len());
                    let mut zipped = im_rc::Vector::new();
                    for i in 0..len {
                        let pair = Rc::new(Object::Comma(
                            list1[i].clone(),
                            list2[i].clone(),
                        ));
                        zipped.push_back(pair);
                    }
                    Ok(Rc::new(Object::List(zipped)))
                }
            )
        );
    }
    fn def_func_functions(&mut self) {
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            let c = tyvar_arena.alloc(TyVarBody::new("c"));
            TypeScheme::forall(
                [a, b, c],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::Var(b)),
                    Type::arrow(
                        Type::arrow(Type::Var(b), Type::Var(c)),
                        Type::arrow(Type::Var(a), Type::Var(c)),
                    ),
                ),
            )
        };
        self.def_func(
            ".>",
            type_scheam,
            curry!([], _runner,
                (Object::Func(f), Object::Func(g)) => {
                    Ok(Rc::new(Object::Func(
                        f.composition(g)
                    )))
                }
            ),
        );
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            let c = tyvar_arena.alloc(TyVarBody::new("c"));
            TypeScheme::forall(
                [a, b, c],
                Type::arrow(
                    Type::arrow(Type::Var(b), Type::Var(c)),
                    Type::arrow(
                        Type::arrow(Type::Var(a), Type::Var(b)),
                        Type::arrow(Type::Var(a), Type::Var(c)),
                    ),
                ),
            )
        };
        self.def_func(
            "<.",
            type_scheam,
            curry!([], _runner,
                (Object::Func(g), Object::Func(f)) => {
                    Ok(Rc::new(Object::Func(
                        f.composition(g)
                    )))
                }
            ),
        );

        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::Var(a),
                    Type::arrow(Type::arrow(Type::Var(a), Type::Var(b)), Type::Var(b)),
                ),
            )
        };
        self.def_func(
            "|>",
            type_scheam,
            curry!([], runner,
                (arg, Object::Func(f)) => {
                    let result = runner.call(&f, Rc::new(arg.clone()))?;
                    Ok(result)
                }
            ),
        );

        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::Var(b)),
                    Type::arrow(Type::Var(a), Type::Var(b)),
                ),
            )
        };
        self.def_func(
            "<|",
            type_scheam,
            curry!([], runner,
                (Object::Func(f), arg) => {
                    let result = runner.call(&f, Rc::new(arg))?;
                    Ok(result)
                }
            ),
        );
        let type_scheam = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            TypeScheme::forall([a], Type::arrow(Type::Var(a), Type::Var(a)))
        };
        self.def_func(
            "id",
            type_scheam,
            native_func!(_runner,
                arg => Ok(Rc::new(arg.clone()))
            ),
        );
    }
    pub fn def_comma_functions(&mut self) {
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::Var(a),
                    Type::arrow(Type::Var(b), Type::comma(Type::Var(a), Type::Var(b))),
                ),
            )
        };
        self.def_func(",", type_scheam, curry!([], _runner,
            (left, right) => {
                Ok(Rc::new(Object::Comma(
                    Rc::new(left.clone()),
                    Rc::new(right.clone()),
                )))
            }
        ));
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(Type::comma(Type::Var(a), Type::Var(b)), Type::Var(a)),
            )
        };
        self.def_func(
            "fst",
            type_scheam,
            native_func!(_runner,
                Object::Comma(left, _right) => {
                    Ok(left.clone())
                }
            ),
        );
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(Type::comma(Type::Var(a), Type::Var(b)), Type::Var(b)),
            )
        };
        self.def_func(
            "snd",
            type_scheam,
            native_func!(_runner,
                Object::Comma(_left, right) => {
                    Ok(right.clone())
                }
            ),
        );
    }
    pub fn def_io_functions(&mut self) {
        self.def_func(
            "print",
            Type::arrow(Type::String, Type::Unit),
            native_func!(_runner,
                Object::String(s) => {
                    println!("{}", s);
                    Ok(Rc::new(Object::Unit))
                }
            ),
        );
    }
    pub fn build(mut self) -> StdLib {
        self.def_add_class();
        self.def_sub_class();
        self.def_mul_class();
        self.def_div_class();
        self.def_mod_class();
        self.def_neg_class();
        self.def_not_class();
        self.def_and_class();
        self.def_or_class();
        self.def_eq_class();
        self.def_len_class();
        self.def_show_class();
        self.def_list_functions();
        self.def_func_functions();
        self.def_comma_functions();
        self.def_io_functions();
        StdLib {
            extern_funcs: self.funcs,
            instance_methods: self.instance_methods,
        }
    }
}
