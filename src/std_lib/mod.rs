use crate::{
    analysis::{
        inference::InferencePool,
        program_data::{Constraint, ConstraintId, InstanceDef, InstanceDefId, VarId},
        types::{
            Instance, InstanceScheme, TyVar, TyVarBody, Type, TypeClass, TypeClassRef, TypeScheme,
        },
    },
    runner::{
        core::{InstanceBody, InstanceDefiner, Runner, Variable},
        obj::{Func, Object},
    },
};
use fxhash::FxHashMap;
use im_rc::{Vector, vector};
use itertools::Itertools;

macro_rules! native_func {
    ($runner_ident:ident, $p:pat => $body:expr) => {
        Object::Func(Func::NativeFunc(Rc::new(
            move |$runner_ident: &mut Runner, arg: Rc<Object>| match &*arg {
                $p => $body,
                #[allow(unreachable_patterns)]
                _ => panic!("invalid argument type for native function"),
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
macro_rules! curry3 {
    ([$($captured:ident),*], $runner_ident: ident, $p:pat => $body:expr) => {
        native_func!(_runner_ident,
            arg0 => {
                let arg0 = arg0.clone();
                $(let $captured = $captured.clone();)*
                Ok(Rc::new(native_func!(_runner_ident,
                    arg1 => {
                        let arg0 = arg0.clone();
                        let arg1 = arg1.clone();
                        Ok(Rc::new(native_func!($runner_ident,
                            arg2 => {
                                let arg0 = arg0.clone();
                                let arg1 = arg1.clone();
                                let arg2 = arg2.clone();
                                match (arg0, arg1, arg2) {
                                    $p => $body,
                                    #[allow(unreachable_patterns)]
                                    _ => panic!("invalid argument types for curried native function"),
                                }
                            }
                        )))
                    }
                )))
            }
        )
    };
}

struct TypeClassBuilder {
    name: Rc<str>,
    bound_vars: Vec<TyVar>,
    methods: FxHashMap<Rc<str>, TypeScheme>,
    method_constraint_ids: FxHashMap<Rc<str>, Vec<ConstraintId>>,
}
impl TypeClassBuilder {
    fn new(name: impl Into<Rc<str>>, bound_vars: Vec<TyVar>) -> Self {
        Self {
            name: name.into(),
            bound_vars,
            methods: FxHashMap::default(),
            method_constraint_ids: FxHashMap::default(),
        }
    }

    fn method(
        mut self,
        name: impl Into<Rc<str>>,
        type_scheme: TypeScheme,
        constraint_ids: Vec<ConstraintId>,
    ) -> Self {
        let name = name.into();
        self.methods.insert(name.clone(), type_scheme);
        self.method_constraint_ids.insert(name, constraint_ids);
        self
    }

    fn build(self) -> TypeClassRef {
        TypeClassRef(Rc::new(TypeClass {
            name: self.name,
            bound_vars: self.bound_vars,
            methods: self.methods,
            method_constraint_ids: self.method_constraint_ids,
        }))
    }
}
struct InstanceBodyBuilder {
    instance: Rc<Instance>,
    method_bodys: FxHashMap<Rc<str>, Variable>,
}
impl InstanceBodyBuilder {
    fn new(instance: Rc<Instance>) -> Self {
        Self {
            instance,
            method_bodys: FxHashMap::default(),
        }
    }

    fn method_body(mut self, name: impl Into<Rc<str>>, body: impl Into<Variable>) -> Self {
        self.method_bodys.insert(name.into(), body.into());
        self
    }

    fn build(self) -> InstanceBody {
        assert!(self.method_bodys.len() == self.instance.class.0.methods.len());
        assert!(
            self.method_bodys
                .keys()
                .all(|name| self.instance.class.0.methods.contains_key(name))
        );
        InstanceBody {
            methods: self.method_bodys,
        }
    }
}

use core::panic;
use std::rc::Rc;
pub struct StdLibDefiner<'a> {
    inference_pool: &'a mut InferencePool,
    funcs: FxHashMap<VarId, (Rc<str>, TypeScheme, Variable)>,
    instance_body_definers: FxHashMap<InstanceDefId, InstanceDefiner>,
}
pub struct StdLib {
    pub extern_funcs: FxHashMap<VarId, (Rc<str>, TypeScheme, Variable)>,
    pub instance_body_definers: FxHashMap<InstanceDefId, InstanceDefiner>,
}
impl<'a> StdLibDefiner<'a> {
    pub fn new(inference_pool: &'a mut InferencePool) -> Self {
        StdLibDefiner {
            inference_pool,
            funcs: FxHashMap::default(),
            instance_body_definers: FxHashMap::default(),
        }
    }
    fn def_type_class(&mut self, type_class: TypeClassRef) {
        self.inference_pool.extern_type_class(type_class);
    }
    fn def_instance(
        &mut self,
        type_class: TypeClassRef,
        assigned_types: impl IntoIterator<Item = Type>,
        instance_body: impl FnOnce(Rc<Instance>) -> InstanceBody,
    ) {
        let instance = Rc::new(Instance {
            class: type_class.clone(),
            assigned_types: assigned_types.into_iter().collect(),
        });
        let instance_def = InstanceDef {
            scheme: InstanceScheme {
                instance: instance.clone(),
                bound_vars: vector![],
                constraints: vector![],
            },
            constraints: vec![],
        };
        let instance_def_id = self.inference_pool.extern_instance(instance_def);
        self.instance_body_definers.insert(
            instance_def_id,
            InstanceDefiner::Just(Rc::new(instance_body(instance))),
        );
    }
    fn def_instance_scheme_without_constraints(
        &mut self,
        type_class: TypeClassRef,
        assigned_types: impl IntoIterator<Item = Type>,
        bound_vars: impl IntoIterator<Item = TyVar>,
        instance_body: impl FnOnce(Rc<Instance>) -> InstanceBody,
    ) {
        let instance = Rc::new(Instance {
            class: type_class.clone(),
            assigned_types: assigned_types.into_iter().collect(),
        });
        let instance_def = InstanceDef {
            scheme: InstanceScheme {
                instance: instance.clone(),
                bound_vars: bound_vars.into_iter().collect(),
                constraints: vector![],
            },
            constraints: vec![],
        };
        let instance_def_id = self.inference_pool.extern_instance(instance_def);
        self.instance_body_definers.insert(
            instance_def_id,
            InstanceDefiner::Just(Rc::new(instance_body(instance))),
        );
    }
    fn def_instance_with_constraints(
        &mut self,
        type_class: TypeClassRef,
        assigned_types: impl IntoIterator<Item = Type>,
        bound_ty_vars: impl IntoIterator<Item = TyVar>,
        constraints: impl IntoIterator<Item = Rc<Instance>>,
        instance_body: impl Fn(Rc<Instance>, &mut Runner, Vec<Rc<InstanceBody>>) -> InstanceBody
        + 'static,
    ) {
        let instance = Rc::new(Instance {
            class: type_class.clone(),
            assigned_types: assigned_types.into_iter().collect(),
        });
        let constraints = constraints.into_iter().collect::<Vector<Rc<Instance>>>();
        let constraint_ids = constraints
            .iter()
            .cloned()
            .map(|instance| {
                self.inference_pool
                    .alloc_constraint(Constraint { instance })
            })
            .collect_vec();
        let instance_def = InstanceDef {
            scheme: InstanceScheme {
                instance: instance.clone(),
                bound_vars: bound_ty_vars.into_iter().collect(),
                constraints,
            },
            constraints: constraint_ids.clone().into_iter().collect(),
        };
        let instance_def_id = self.inference_pool.extern_instance(instance_def);
        self.instance_body_definers.insert(
            instance_def_id,
            InstanceDefiner::WithConstraintAssign(Rc::new(move |runner, constraint_assign| {
                let assigned_instances = constraint_ids
                    .iter()
                    .map(|cid| constraint_assign.get(cid).unwrap().clone())
                    .map(|inst_ref| runner.get_instance_body(inst_ref))
                    .collect_vec();
                Rc::new(instance_body(instance.clone(), runner, assigned_instances))
            })),
        );
    }
    fn def_func(
        &mut self,
        name: impl Into<Rc<str>>,
        type_scheme: impl Into<TypeScheme>,
        obj: impl Into<Rc<Object>>,
    ) {
        let name = name.into();
        let type_scheme = type_scheme.into();
        let obj = obj.into();
        let var_id = self
            .inference_pool
            .extern_func(name.clone(), type_scheme.clone(), vector![]);

        self.funcs.insert(var_id, (name, type_scheme, obj.into()));
    }
    fn def_func_with_constraints(
        &mut self,
        name: impl Into<Rc<str>>,
        type_scheme: impl Into<TypeScheme>,
        obj: impl Fn(&mut Runner, Vec<Rc<InstanceBody>>) -> Rc<Object> + 'static,
    ) {
        let name = name.into();
        let type_scheme = type_scheme.into();

        let constraint_ids = type_scheme
            .constraints
            .iter()
            .cloned()
            .map(|instance| {
                self.inference_pool
                    .alloc_constraint(Constraint { instance })
            })
            .collect::<Vector<ConstraintId>>();

        let var_id = self.inference_pool.extern_func(
            name.clone(),
            type_scheme.clone(),
            constraint_ids.clone(),
        );

        self.funcs.insert(
            var_id,
            (
                name,
                type_scheme,
                Variable::Def(Rc::new(move |runner: &mut Runner, instance_replace| {
                    let assigned_instances = constraint_ids
                        .iter()
                        .map(|cid| {
                            instance_replace
                                .get(cid)
                                .expect("instance not found in replace map")
                                .clone()
                        })
                        .map(|inst_ref| runner.get_instance_body(inst_ref))
                        .collect_vec();
                    Ok(obj(runner, assigned_instances))
                })),
            ),
        );
    }
    fn def_show_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let show_class = TypeClassBuilder::new("Show", vec![a])
            .method(
                "show",
                TypeScheme::forall([], Type::arrow(Type::Var(a), Type::String)),
                vec![],
            )
            .build();
        self.def_type_class(show_class.clone());

        // Show for Int
        self.def_instance(show_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "show",
                    native_func!(_runner,
                        Object::Int(n) => {
                            Ok(Rc::new(Object::String(Rc::new(n.to_string()))))
                        }
                    ),
                )
                .build()
        });

        //Show for Float
        self.def_instance(show_class.clone(), [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "show",
                    native_func!(_runner,
                        Object::Float(n) => {
                            Ok(Rc::new(Object::String(Rc::new(n.to_string()))))
                        }
                    ),
                )
                .build()
        });

        //Show for Bool
        self.def_instance(show_class.clone(), [Type::Bool], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "show",
                    native_func!(_runner,
                        Object::Bool(b) => {
                            Ok(Rc::new(Object::String(Rc::new(b.to_string()))))
                        }
                    ),
                )
                .build()
        });

        // Show for String
        self.def_instance(show_class.clone(), [Type::String], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "show",
                    native_func!(_runner,
                        Object::String(s) => {
                            Ok(Rc::new(Object::String(Rc::new(format!("\"{}\"", s.escape_debug())))))
                        }
                    ),
                )
                .build()
        });

        // Show for Unit
        self.def_instance(show_class.clone(), [Type::Unit], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "show",
                    native_func!(_runner,
                        Object::Unit => {
                            Ok(Rc::new(Object::String(Rc::new("()".into()))))
                        }
                    ),
                )
                .build()
        });

        // Show for List
        let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
        self.def_instance_with_constraints(
            show_class.clone(),
            [Type::List(Type::Var(b).into())],
            [b],
            [Instance {
                class: show_class.clone(),
                assigned_types: vector![Type::Var(b)],
            }
            .into()],
            |instance, runner, constraints| {
                let show_b_body = constraints[0].methods["show"].clone();
                let show_func = runner
                    .read_var(&show_b_body, im_rc::HashMap::default())
                    .unwrap();
                let Object::Func(show_b) = &*show_func else {
                    panic!("expected function for show method")
                };
                let show_b = show_b.clone();
                InstanceBodyBuilder::new(instance)
                    .method_body(
                        "show",
                        Variable::Var(Rc::new(native_func!(runner,
                            Object::List(list) => {
                                let mut s = String::from("[");
                                for (i, item) in list.iter().enumerate() {
                                    let shown_item = runner.call(&show_b, item.clone())?;
                                    let Object::String(shown_item) = &*shown_item else {
                                        panic!("expected String from show method")
                                    };
                                    if i == 0 {
                                        s.push_str(shown_item);
                                    } else {
                                        s.push_str(", ");
                                        s.push_str(shown_item);
                                    }
                                }
                                s.push(']');
                                Ok(Rc::new(Object::String(Rc::new(s))))
                            }
                        ))),
                    )
                    .build()
            },
        );

        // Show for Comma
        let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
        let c = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("c"));
        self.def_instance_with_constraints(
            show_class.clone(),
            [Type::Comma(Type::Var(b).into(), Type::Var(c).into())],
            [b, c],
            [
                Instance {
                    class: show_class.clone(),
                    assigned_types: vector![Type::Var(b)],
                }
                .into(),
                Instance {
                    class: show_class.clone(),
                    assigned_types: vector![Type::Var(c)],
                }
                .into(),
            ],
            |instance, runner, constraints| {
                let show_b_body = constraints[0].methods["show"].clone();
                let show_c_body = constraints[1].methods["show"].clone();
                let show_b_func = runner
                    .read_var(&show_b_body, im_rc::HashMap::default())
                    .unwrap();
                let show_c_func = runner
                    .read_var(&show_c_body, im_rc::HashMap::default())
                    .unwrap();
                let Object::Func(show_b) = &*show_b_func else {
                    panic!("expected function for show method")
                };
                let Object::Func(show_c) = &*show_c_func else {
                    panic!("expected function for show method")
                };
                let show_b = show_b.clone();
                let show_c = show_c.clone();
                InstanceBodyBuilder::new(instance)
                    .method_body(
                        "show",
                        Variable::Var(Rc::new(native_func!(runner,
                            Object::Comma(l, r) => {
                                let shown_l = runner.call(&show_b, l.clone())?;
                                let shown_r = runner.call(&show_c, r.clone())?;
                                let Object::String(shown_l) = &*shown_l else {
                                    panic!("expected String from show method")
                                };
                                let Object::String(shown_r) = &*shown_r else {
                                    panic!("expected String from show method")
                                };
                                Ok(Rc::new(Object::String(Rc::new(format!("({}, {})", shown_l, shown_r)))))
                            }
                        ))),
                    )
                    .build()
            }
        );

        let type_scheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            let constraint = Rc::new(Instance {
                class: show_class.clone(),
                assigned_types: vector![Type::Var(a)],
            });
            TypeScheme::forall_with_constraints(
                [a],
                Type::arrow(Type::Var(a), Type::Unit),
                [constraint],
            )
        };
        self.def_func_with_constraints("print", type_scheme, |runner, constraints| {
            let show_a = constraints[0].methods["show"].clone();
            let show_a = runner.read_var(&show_a, im_rc::HashMap::default()).unwrap();
            let Object::Func(show_a) = &*show_a else {
                panic!("expected function for show method")
            };
            let show_a = show_a.clone();
            Rc::new(native_func!(_runner,
                arg => {
                    let shown = _runner.call(&show_a, Rc::new(arg.clone()))?;
                    let Object::String(shown) = &*shown else {
                        panic!("expected String from show method")
                    };
                    println!("{}", shown);
                    Ok(Rc::new(Object::Unit))
                }
            ))
        });
    }
    fn def_add_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let add_class = TypeClassBuilder::new("Add", vec![a])
            .method(
                "+",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(add_class.clone());

        // Add for Int
        self.def_instance(add_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "+",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x + y)))
                        }
                    )),
                )
                .build()
        });

        // Add for Float
        self.def_instance(add_class.clone(), [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "+",
                    Rc::new(curry!([], _runner,
                        (Object::Float(x), Object::Float(y)) => {
                            Ok(Rc::new(Object::Float(x + y)))
                        }
                    )),
                )
                .build()
        });

        // Add for String
        self.def_instance(add_class.clone(), [Type::String], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "+",
                    Rc::new(curry!([], _runner,
                        (Object::String(x), Object::String(y)) => {
                            Ok(Rc::new(Object::String(Rc::new(Rc::unwrap_or_clone(x) + &y))))
                        }
                    )),
                )
                .build()
        });

        // Add for List
        let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
        self.def_instance_scheme_without_constraints(
            add_class,
            [Type::List(Rc::new(Type::Var(b)))],
            [b],
            |instance| {
                InstanceBodyBuilder::new(instance)
                    .method_body(
                        "+",
                        Rc::new(curry!([], _runner,
                            (Object::List(mut x), Object::List(y)) => {
                                x.append(y);
                                Ok(Rc::new(Object::List(x)))
                            }
                        )),
                    )
                    .build()
            },
        );
    }
    fn def_sub_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let sub_class = TypeClassBuilder::new("Sub", vec![a])
            .method(
                "-",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(sub_class.clone());

        // Sub for Int
        self.def_instance(sub_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "-",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x - y)))
                        }
                    )),
                )
                .build()
        });

        // Sub for Float
        self.def_instance(sub_class, [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "-",
                    Rc::new(curry!([], _runner,
                        (Object::Float(x), Object::Float(y)) => {
                            Ok(Rc::new(Object::Float(x - y)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_mul_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let mul_class = TypeClassBuilder::new("Mul", vec![a])
            .method(
                "*",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(mul_class.clone());

        // Mul for Int
        self.def_instance(mul_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "*",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x * y)))
                        }
                    )),
                )
                .build()
        });
        // Mul for Float
        self.def_instance(mul_class, [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "*",
                    Rc::new(curry!([], _runner,
                        (Object::Float(x), Object::Float(y)) => {
                            Ok(Rc::new(Object::Float(x * y)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_div_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let div_class = TypeClassBuilder::new("Div", vec![a])
            .method(
                "/",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(div_class.clone());

        // Div for Int
        self.def_instance(div_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "/",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x / y)))
                        }
                    )),
                )
                .build()
        });
        // Div for Float
        self.def_instance(div_class, [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "/",
                    Rc::new(curry!([], _runner,
                        (Object::Float(x), Object::Float(y)) => {
                            Ok(Rc::new(Object::Float(x / y)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_mod_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let mod_class = TypeClassBuilder::new("Mod", vec![a])
            .method(
                "%",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(mod_class.clone());

        // Mod for Int
        self.def_instance(mod_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "%",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x % y)))
                        }
                    )),
                )
                .build()
        });
        // Mod for Float
        self.def_instance(mod_class, [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "%",
                    Rc::new(curry!([], _runner,
                        (Object::Float(x), Object::Float(y)) => {
                            Ok(Rc::new(Object::Float(x % y)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_neg_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let neg_class = TypeClassBuilder::new("Neg", vec![a])
            .method(
                "-_",
                TypeScheme::forall([], Type::arrow(Type::Var(a), Type::Var(a))),
                vec![],
            )
            .build();
        self.def_type_class(neg_class.clone());

        // Neg for Int
        self.def_instance(neg_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "-_",
                    native_func!(_runner,
                        Object::Int(x) => {
                            Ok(Rc::new(Object::Int(-x)))
                        }
                    ),
                )
                .build()
        });
        // Neg for Float
        self.def_instance(neg_class, [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "-_",
                    native_func!(_runner,
                        Object::Float(x) => {
                            Ok(Rc::new(Object::Float(-x)))
                        }
                    ),
                )
                .build()
        });
    }
    fn def_not_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let not_class = TypeClassBuilder::new("Not", vec![a])
            .method(
                "!_",
                TypeScheme::forall([], Type::arrow(Type::Var(a), Type::Var(a))),
                vec![],
            )
            .build();
        self.def_type_class(not_class.clone());

        // Not for Bool
        self.def_instance(not_class.clone(), [Type::Bool], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "!_",
                    native_func!(_runner,
                        Object::Bool(b) => {
                            Ok(Rc::new(Object::Bool(!b)))
                        }
                    ),
                )
                .build()
        });
        // Not for Int
        self.def_instance(not_class, [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "!_",
                    native_func!(_runner,
                        Object::Int(x) => {
                            Ok(Rc::new(Object::Int(!x)))
                        }
                    ),
                )
                .build()
        });
    }
    fn def_and_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let and_class = TypeClassBuilder::new("And", vec![a])
            .method(
                "&",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(and_class.clone());

        // And for Bool
        self.def_instance(and_class.clone(), [Type::Bool], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "&",
                    Rc::new(curry!([], _runner,
                        (Object::Bool(x), Object::Bool(y)) => {
                            Ok(Rc::new(Object::Bool(x & y)))
                        }
                    )),
                )
                .build()
        });
        // And for Int
        self.def_instance(and_class, [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "&",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x & y)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_or_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let or_class = TypeClassBuilder::new("Or", vec![a])
            .method(
                "|",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Var(a))),
                ),
                vec![],
            )
            .build();
        self.def_type_class(or_class.clone());

        // Or for Bool
        self.def_instance(or_class.clone(), [Type::Bool], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "|",
                    Rc::new(curry!([], _runner,
                        (Object::Bool(x), Object::Bool(y)) => {
                            Ok(Rc::new(Object::Bool(x | y)))
                        }
                    )),
                )
                .build()
        });
        // Or for Int
        self.def_instance(or_class, [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "|",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Int(x | y)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_eq_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let eq_class = TypeClassBuilder::new("Eq", vec![a])
            .method(
                "==",
                TypeScheme::forall(
                    [],
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Bool)),
                ),
                vec![],
            )
            .build();
        self.def_type_class(eq_class.clone());

        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let constraint = Rc::new(Instance {
            class: eq_class.clone(),
            assigned_types: vector![Type::Var(a)],
        });
        self.def_func_with_constraints(
            "!=",
            TypeScheme::forall_with_constraints(
                [a],
                Type::arrow(Type::Var(a), Type::arrow(Type::Var(a), Type::Bool)),
                [constraint.clone()],
            ),
            |_runner, instances| {
                let eq_instance_body = instances[0].clone();
                Rc::new(curry!([eq_instance_body], runner,
                    (arg1, arg2) => {
                        let eq_func = eq_instance_body.methods.get("==").expect("method '==' not found in Eq instance");
                        let eq_func = runner.read_var(eq_func, im_rc::HashMap::default())?;
                        let Object::Func(eq_func) = eq_func.as_ref() else {
                            panic!("method '==' is not a function");
                        };
                        let f = runner.call(eq_func, Rc::new(arg1))?;
                        let Object::Func(f) = f.as_ref() else {
                            panic!("method '==' did not return a function");
                        };
                        let eq_result = runner.call(f, Rc::new(arg2))?;
                        match &*eq_result {
                            Object::Bool(b) => Ok(Rc::new(Object::Bool(!b))),
                            _ => panic!("Eq '==' method did not return Bool"),
                        }
                    }))
            }
        );

        // Eq for Int
        self.def_instance(eq_class.clone(), [Type::Int], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "==",
                    Rc::new(curry!([], _runner,
                        (Object::Int(x), Object::Int(y)) => {
                            Ok(Rc::new(Object::Bool(x == y)))
                        }
                    )),
                )
                .build()
        });
        // Eq for Float
        self.def_instance(eq_class.clone(), [Type::Float], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "==",
                    Rc::new(curry!([], _runner,
                        (Object::Float(x), Object::Float(y)) => {
                            Ok(Rc::new(Object::Bool(x == y)))
                        }
                    )),
                )
                .build()
        });
        //Eq for Bool
        self.def_instance(eq_class.clone(), [Type::Bool], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "==",
                    Rc::new(curry!([], _runner,
                        (Object::Bool(x), Object::Bool(y)) => {
                            Ok(Rc::new(Object::Bool(x == y)))
                        }
                    )),
                )
                .build()
        });
        //Eq for String
        self.def_instance(eq_class.clone(), [Type::String], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "==",
                    Rc::new(curry!([], _runner,
                            (Object::String(x), Object::String(y)) => {
                                Ok(Rc::new(Object::Bool(x == y)))
                            }
                    )),
                )
                .build()
        });
        //Eq for Unit
        self.def_instance(eq_class, [Type::Unit], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "==",
                    Rc::new(curry!([], _runner,
                        (Object::Unit, Object::Unit) => {
                            Ok(Rc::new(Object::Bool(true)))
                        }
                    )),
                )
                .build()
        });
    }
    fn def_len_class(&mut self) {
        let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
        let len_class = TypeClassBuilder::new("Len", vec![a])
            .method(
                "len",
                TypeScheme::forall([], Type::arrow(Type::Var(a), Type::Int)),
                vec![],
            )
            .build();
        self.def_type_class(len_class.clone());

        // Len for String
        self.def_instance(len_class.clone(), [Type::String], |instance| {
            InstanceBodyBuilder::new(instance)
                .method_body(
                    "len",
                    native_func!(_runner,
                        Object::String(s) => {
                            Ok(Rc::new(Object::Int(s.len() as i64)))
                        }
                    ),
                )
                .build()
        });
        // Len for List
        let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
        self.def_instance_scheme_without_constraints(
            len_class.clone(),
            [Type::list(Type::Var(b))],
            [b],
            |instance| {
                InstanceBodyBuilder::new(instance)
                    .method_body(
                        "len",
                        native_func!(_runner,
                            Object::List(elems) => {
                                Ok(Rc::new(Object::Int(elems.len() as i64)))
                            }
                        ),
                    )
                    .build()
            },
        );
    }
    fn def_list_functions(&mut self) {
        let type_sheme = {
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
            type_sheme,
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

        let type_sheme = {
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
            type_sheme,
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
        let type_sheme = {
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
        self.def_func(
            "zip",
            type_sheme,
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
            ),
        );

        // (a -> b -> c) -> [a] -> [b] -> [c]
        let type_sheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
            let c = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("c"));
            TypeScheme::forall(
                [a, b, c],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(b), Type::Var(c))),
                    Type::arrow(
                        Type::list(Type::Var(a)),
                        Type::arrow(Type::list(Type::Var(b)), Type::list(Type::Var(c))),
                    ),
                ),
            )
        };
        self.def_func(
            "zipWith",
            type_sheme,
            curry3!([], _runner,
                (Object::Func(f), Object::List(list1), Object::List(list2)) => {
                    let len = std::cmp::min(list1.len(), list2.len());
                    let mut zipped = im_rc::Vector::new();
                    for i in 0..len {
                        let applied = _runner.call(&f, list1[i].clone())?;
                        let Object::Func(f2) = &*applied else {
                            panic!("zipWith function did not return a function");
                        };
                        let result = _runner.call(f2, list2[i].clone())?;
                        zipped.push_back(result);
                    }
                    Ok(Rc::new(Object::List(zipped)))
                }
            ),
        );
    }
    fn def_func_functions(&mut self) {
        let type_sheme = {
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
            type_sheme,
            curry!([], _runner,
                (Object::Func(f), Object::Func(g)) => {
                    Ok(Rc::new(Object::Func(
                        f.composition(g)
                    )))
                }
            ),
        );
        let type_sheme = {
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
            type_sheme,
            curry!([], _runner,
                (Object::Func(g), Object::Func(f)) => {
                    Ok(Rc::new(Object::Func(
                        f.composition(g)
                    )))
                }
            ),
        );

        let type_sheme = {
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
            type_sheme,
            curry!([], runner,
                (arg, Object::Func(f)) => {
                    let result = runner.call(&f, Rc::new(arg.clone()))?;
                    Ok(result)
                }
            ),
        );

        let type_sheme = {
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
            type_sheme,
            curry!([], runner,
                (Object::Func(f), arg) => {
                    let result = runner.call(&f, Rc::new(arg))?;
                    Ok(result)
                }
            ),
        );
        let type_sheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            TypeScheme::forall([a], Type::arrow(Type::Var(a), Type::Var(a)))
        };
        self.def_func(
            "id",
            type_sheme,
            native_func!(_runner,
                arg => Ok(Rc::new(arg.clone()))
            ),
        );

        let type_scheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(Type::Var(a), Type::arrow(Type::Var(b), Type::Var(a))),
            )
        };
        self.def_func(
            "const",
            type_scheme,
            curry!([], _runner,
                (arg1, _arg2) => {
                    Ok(Rc::new(arg1.clone()))
                }
            ),
        );

        let type_scheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
            let c = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("c"));
            TypeScheme::forall(
                [a, b, c],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(b), Type::Var(c))),
                    Type::arrow(Type::Var(b), Type::arrow(Type::Var(a), Type::Var(c))),
                ),
            )
        };
        self.def_func(
            "flip",
            type_scheme,
            curry3!([], runner,
                (Object::Func(f), y, x) => {
                    let result = runner.call(&f, Rc::new(x.clone()))?;
                    let Object::Func(f2) = &*result else {
                        panic!("expected function from flip");
                    };
                    let final_result = runner.call(f2, Rc::new(y.clone()))?;
                    Ok(final_result)
                }
            ),
        );

        let type_scheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            TypeScheme::forall(
                [a],
                Type::arrow(
                    Type::Bool,
                    Type::arrow(
                        Type::arrow(Type::Unit, Type::Var(a)),
                        Type::arrow(Type::arrow(Type::Unit, Type::Var(a)), Type::Var(a)),
                    ),
                ),
            )
        };
        self.def_func(
            "if",
            type_scheme,
            curry3!([], runner,
                (Object::Bool(cond), Object::Func(then_branch), Object::Func(else_branch)) => {
                    if cond {
                        runner.call(&then_branch, Rc::new(Object::Unit))
                    } else {
                        runner.call(&else_branch, Rc::new(Object::Unit))
                    }
                }
            ),
        );

        // ((a, b) -> c) -> a -> b -> c
        let type_scheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
            let c = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("c"));
            TypeScheme::forall(
                [a, b, c],
                Type::arrow(
                    Type::arrow(Type::comma(Type::Var(a), Type::Var(b)), Type::Var(c)),
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(b), Type::Var(c))),
                ),
            )
        };
        self.def_func(
            "curry",
            type_scheme,
            curry3!([], runner,
                (Object::Func(f), arg1, arg2) => {
                    let comma_arg = Rc::new(Object::Comma(Rc::new(arg1.clone()), Rc::new(arg2.clone())));
                    let result = runner.call(&f, comma_arg)?;
                    Ok(result)
                }
            ),
        );

        // (a -> b -> c) -> (a, b) -> c
        let type_scheme = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            let b = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("b"));
            let c = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("c"));
            TypeScheme::forall(
                [a, b, c],
                Type::arrow(
                    Type::arrow(Type::Var(a), Type::arrow(Type::Var(b), Type::Var(c))),
                    Type::arrow(Type::comma(Type::Var(a), Type::Var(b)), Type::Var(c)),
                ),
            )
        };
        self.def_func(
            "uncurry",
            type_scheme,
            curry!([], runner,
                (Object::Func(f), Object::Comma(arg1, arg2)) => {
                    let result1 = runner.call(&f, arg1.clone())?;
                    let Object::Func(f2) = &*result1 else {
                        panic!("expected function from uncurry");
                    };
                    let final_result = runner.call(f2, arg2.clone())?;
                    Ok(final_result)
                }
            ),
        );
    }
    pub fn def_comma_functions(&mut self) {
        let type_sheme = {
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
        self.def_func(
            ",",
            type_sheme,
            curry!([], _runner,
                (left, right) => {
                    Ok(Rc::new(Object::Comma(
                        Rc::new(left.clone()),
                        Rc::new(right.clone()),
                    )))
                }
            ),
        );
        let type_sheme = {
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
            type_sheme,
            native_func!(_runner,
                Object::Comma(left, _right) => {
                    Ok(left.clone())
                }
            ),
        );
        let type_sheme = {
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
            type_sheme,
            native_func!(_runner,
                Object::Comma(_left, right) => {
                    Ok(right.clone())
                }
            ),
        );
    }
    pub fn def_io_functions(&mut self) {
        self.def_func(
            "putStrLn",
            Type::arrow(Type::String, Type::Unit),
            native_func!(_runner,
                Object::String(s) => {
                    println!("{}", s);
                    Ok(Rc::new(Object::Unit))
                }
            ),
        );
        self.def_func(
            "putStr",
            Type::arrow(Type::String, Type::Unit),
            native_func!(_runner,
                Object::String(s) => {
                    print!("{}", s);
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
            instance_body_definers: self.instance_body_definers,
        }
    }
}
