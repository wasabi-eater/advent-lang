use crate::{
    analysis::{
        inference::InferencePool,
        types::{TyVarBody, Type, TypeScheme, VarId},
    },
    runner,
};
use fxhash::FxHashMap;

macro_rules! native_func {
    ($runner_ident:ident, $p:pat => $body:expr) => {
        runner::obj::Object::Func(runner::obj::Func::NativeFunc(Rc::new(
            move |$runner_ident: &mut runner::core::Runner, arg: Rc<runner::obj::Object>| {
                match &*arg {
                    $p => $body,
                    #[allow(unreachable_patterns)]
                    _ => panic!("invalid argument type for native function"),
                }
            },
        )))
    };
}

use std::rc::Rc;
pub struct StdLibDefiner<'a> {
    inference_pool: &'a mut InferencePool,
    funcs: FxHashMap<VarId, (Rc<str>, TypeScheme, Rc<runner::obj::Object>)>,
}
impl<'a> StdLibDefiner<'a> {
    pub fn new(inference_pool: &'a mut InferencePool) -> Self {
        let stdlib = StdLibDefiner {
            inference_pool,
            funcs: FxHashMap::default(),
        };
        stdlib
    }
    pub fn def_func(
        &mut self,
        name: impl Into<Rc<str>>,
        type_scheme: impl Into<TypeScheme>,
        obj: impl Into<Rc<runner::obj::Object>>,
    ) {
        let name = name.into();
        let type_scheme = type_scheme.into();
        let var_id = self
            .inference_pool
            .extern_func(name.clone(), type_scheme.clone());

        self.funcs
            .insert(var_id, (name, type_scheme.into(), obj.into()));
    }
    fn def_int_functions(&mut self) {
        self.def_func(
            "+",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Int(a + b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "-",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Int(a - b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "*",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Int(a * b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "/",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Int(a / b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "==",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Bool(a == *b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "-_",
            Type::arrow(Type::Int, Type::Int),
            native_func!(_runner,
                runner::obj::Object::Int(a) => Ok(Rc::new(runner::obj::Object::Int(-a)))
            ),
        );
        self.def_func(
            "!_",
            Type::arrow(Type::Int, Type::Int),
            native_func!(_runner,
                runner::obj::Object::Int(a) => Ok(Rc::new(runner::obj::Object::Int(!a)))
            ),
        );
        self.def_func(
            "&",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Int(a & *b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "|",
            Type::arrow(Type::Int, Type::arrow(Type::Int, Type::Int)),
            native_func!(_runner,
                runner::obj::Object::Int(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Int(b) => {
                            Ok(Rc::new(runner::obj::Object::Int(a | b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "show",
            Type::arrow(Type::Int, Type::String),
            native_func!(_runner,
                runner::obj::Object::Int(n) => {
                    Ok(Rc::new(runner::obj::Object::String(Rc::new(n.to_string()))))
                }
            ),
        );
    }
    fn def_float_functions(&mut self) {
        self.def_func(
            "+",
            Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)),
            native_func!(_runner,
                runner::obj::Object::Float(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Float(b) => {
                            Ok(Rc::new(runner::obj::Object::Float(a + b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "-",
            Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)),
            native_func!(_runner,
                runner::obj::Object::Float(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Float(b) => {
                            Ok(Rc::new(runner::obj::Object::Float(a - b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "*",
            Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)),
            native_func!(_runner,
                runner::obj::Object::Float(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Float(b) => {
                            Ok(Rc::new(runner::obj::Object::Float(a * b)))
                        }
                    )))
                }
            ),
        );

        self.def_func(
            "/",
            Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Float)),
            native_func!(_runner,
                runner::obj::Object::Float(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Float(b) => {
                            Ok(Rc::new(runner::obj::Object::Float(a / b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "==",
            Type::arrow(Type::Float, Type::arrow(Type::Float, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::Float(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Float(b) => {
                            Ok(Rc::new(runner::obj::Object::Bool(a == *b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "-_",
            Type::arrow(Type::Float, Type::Float),
            native_func!(_runner,
                runner::obj::Object::Float(a) => Ok(Rc::new(runner::obj::Object::Float(-a)))
            ),
        );
        self.def_func(
            "show",
            Type::arrow(Type::Float, Type::String),
            native_func!(_runner,
                runner::obj::Object::Float(n) => {
                    Ok(Rc::new(runner::obj::Object::String(Rc::new(n.to_string()))))
                }
            ),
        );
    }
    fn def_bool_functions(&mut self) {
        self.def_func(
            "==",
            Type::arrow(Type::Bool, Type::arrow(Type::Bool, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::Bool(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Bool(b) => {
                            Ok(Rc::new(runner::obj::Object::Bool(a == *b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "!_",
            Type::arrow(Type::Bool, Type::Bool),
            native_func!(_runner,
                runner::obj::Object::Bool(a) => Ok(Rc::new(runner::obj::Object::Bool(!a)))
            ),
        );
        self.def_func(
            "&",
            Type::arrow(Type::Bool, Type::arrow(Type::Bool, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::Bool(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Bool(b) => {
                            Ok(Rc::new(runner::obj::Object::Bool(a & b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "|",
            Type::arrow(Type::Bool, Type::arrow(Type::Bool, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::Bool(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Bool(b) => {
                            Ok(Rc::new(runner::obj::Object::Bool(a | b)))
                        }
                    )))
                }
            ),
        );
        
        self.def_func(
            "show",
            Type::arrow(Type::Bool, Type::String),
            native_func!(_runner,
                runner::obj::Object::Bool(b) => {
                    Ok(Rc::new(runner::obj::Object::String(Rc::new(b.to_string()))))
                }
            ),
        );
    }
    fn def_str_functions(&mut self) {
        self.def_func(
            "+",
            Type::arrow(Type::String, Type::arrow(Type::String, Type::String)),
            native_func!(_runner,
                runner::obj::Object::String(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::String(b) => {
                            Ok(Rc::new(runner::obj::Object::String(Rc::new(format!("{}{}", a, b)))))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "==",
            Type::arrow(Type::String, Type::arrow(Type::String, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::String(a) => {
                    let a = a.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::String(b) => {
                            Ok(Rc::new(runner::obj::Object::Bool(a == *b)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "show",
            Type::arrow(Type::String, Type::String),
            native_func!(_runner,
                runner::obj::Object::String(s) => {
                    Ok(Rc::new(runner::obj::Object::String(s.clone())))
                }
            ),
        );
        self.def_func("len", Type::arrow(Type::String, Type::Int),
            native_func!(_runner,
                runner::obj::Object::String(s) => {
                    Ok(Rc::new(runner::obj::Object::Int(s.len() as i64)))
                }
            ),
        );
    }
    fn def_list_functions(&mut self) {
        let type_scheam = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            TypeScheme::forall(
                [a],
                Type::arrow(Type::list(Type::Var(a)), Type::list(Type::Var(a))),
            )
        };
        self.def_func(
            "+",
            type_scheam,
            native_func!(_runner,
                runner::obj::Object::List(elems) => {
                    let elems = elems.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::List(elems2) => {
                            let mut new_elems = elems.clone();
                            new_elems.extend(elems2.iter().cloned());
                            Ok(Rc::new(runner::obj::Object::List(new_elems)))
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
                    Type::arrow(Type::Var(a), Type::Var(b)),
                    Type::arrow(Type::list(Type::Var(a)), Type::list(Type::Var(b))),
                ),
            )
        };
        self.def_func(
            "map",
            type_scheam,
            native_func!(_runner,
                runner::obj::Object::Func(f) => {
                    let f = f.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::List(elems) => {
                            let mut new_elems = im_rc::Vector::new();
                            for elem in elems.iter() {
                                let mapped = _runner.call(&f, elem.clone())?;
                                new_elems.push_back(mapped);
                            }
                            Ok(Rc::new(runner::obj::Object::List(new_elems)))
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
                runner::obj::Object::Func(f) => {
                    let f = f.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::List(elems) => {
                            let mut new_elems = im_rc::Vector::new();
                            for elem in elems.iter() {
                                let pred = _runner.call(&f, elem.clone())?;
                                if let runner::obj::Object::Bool(b) = *pred {
                                    if b {
                                        new_elems.push_back(elem.clone());
                                    }
                                } else {
                                    panic!("filter predicate must return a boolean");
                                }
                            }
                            Ok(Rc::new(runner::obj::Object::List(new_elems)))
                        }
                    )))
                }
            ),
        );
        let type_scheam = {
            let a = self.inference_pool.tyvar_arena().alloc(TyVarBody::new("a"));
            TypeScheme::forall(
                [a],
                Type::arrow(Type::list(Type::Var(a)), Type::Int),
            )
        };
        self.def_func("len", type_scheam,
            native_func!(_runner,
                runner::obj::Object::List(elems) => {
                    Ok(Rc::new(runner::obj::Object::Int(elems.len() as i64)))
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
                    Type::arrow(Type::list(Type::Var(b)), Type::list(Type::comma(Type::Var(a), Type::Var(b)))),
                ),
            )
        };
        self.def_func("zip", type_scheam,
            native_func!(_runner,
                runner::obj::Object::List(elems) => {
                    let elems = elems.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::List(elems2) => {
                            let elems2 = elems2.clone();
                            let min_len = elems.len().min(elems2.len());
                            let mut new_elems = im_rc::Vector::new();
                            for i in 0..min_len {
                                let left = elems.get(i).unwrap().clone();
                                let right = elems2.get(i).unwrap().clone();
                                new_elems.push_back(Rc::new(runner::obj::Object::Comma(left, right)));
                            }
                            Ok(Rc::new(runner::obj::Object::List(new_elems)))
                        }
                    )))
                }
            ),
        );
    }
    fn def_unit_functions(&mut self) {
        self.def_func(
            "==",
            Type::arrow(Type::Unit, Type::arrow(Type::Unit, Type::Bool)),
            native_func!(_runner,
                runner::obj::Object::Unit => {
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Unit => {
                            Ok(Rc::new(runner::obj::Object::Bool(true)))
                        }
                    )))
                }
            ),
        );
        self.def_func(
            "show",
            Type::arrow(Type::Unit, Type::String),
            native_func!(_runner,
                runner::obj::Object::Unit => {
                    Ok(Rc::new(runner::obj::Object::String(Rc::new("()".to_string()))))
                }
            ),
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
            native_func!(_runner,
                runner::obj::Object::Func(f) => {
                    let f = f.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Func(g) => {
                            Ok(Rc::new(runner::obj::Object::Func(
                                f.clone().composition(g.clone())
                            )))
                        }
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
            native_func!(_runner,
                runner::obj::Object::Func(g) => {
                    let g = g.clone();
                    Ok(Rc::new(native_func!(_runner,
                        runner::obj::Object::Func(f) => {
                            Ok(Rc::new(runner::obj::Object::Func(
                                f.clone().composition(g.clone())
                            )))
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
                    Type::Var(a),
                    Type::arrow(Type::arrow(Type::Var(a), Type::Var(b)), Type::Var(b)),
                ),
            )
        };
        self.def_func(
            "|>",
            type_scheam,
            native_func!(_runner,
                arg => {
                    let arg = arg.clone();
                    Ok(Rc::new(
                        native_func!(_runner,
                            runner::obj::Object::Func(f) => {
                                let result = _runner.call(&f, Rc::new(arg.clone()))?;
                                Ok(result)
                            }
                        )
                    ))
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
            native_func!(_runner,
                runner::obj::Object::Func(f) => {
                    let f = f.clone();
                    Ok(Rc::new(native_func!(_runner,
                        arg => {
                            let result = _runner.call(&f, Rc::new(arg.clone()))?;
                            Ok(result)
                        }
                    )))
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
        self.def_func(",", type_scheam, native_func!(_runner,
            left => {
                let left = left.clone();
                Ok(Rc::new(native_func!(_runner,
                    right => {
                        let right = right.clone();
                        Ok(Rc::new(runner::obj::Object::Comma(Rc::new(left.clone()), Rc::new(right.clone()))))
                    }
                )))
            }
        ));
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::comma(Type::Var(a), Type::Var(b)),
                    Type::Var(a),
                ),
            )
        };
        self.def_func("fst", type_scheam, native_func!(_runner,
            runner::obj::Object::Comma(left, _right) => {
                Ok(left.clone())
            }
        ));
        let type_scheam = {
            let tyvar_arena = self.inference_pool.tyvar_arena();
            let a = tyvar_arena.alloc(TyVarBody::new("a"));
            let b = tyvar_arena.alloc(TyVarBody::new("b"));
            TypeScheme::forall(
                [a, b],
                Type::arrow(
                    Type::comma(Type::Var(a), Type::Var(b)),
                    Type::Var(b),
                ),
            )
        };
        self.def_func("snd", type_scheam, native_func!(_runner,
            runner::obj::Object::Comma(_left, right) => {
                Ok(right.clone())
            }
        ));
    }
    pub fn def_io_functions(&mut self) {
        self.def_func(
            "print",
            Type::arrow(Type::String, Type::Unit),
            native_func!(_runner,
                runner::obj::Object::String(s) => {
                    println!("{}", s);
                    Ok(Rc::new(runner::obj::Object::Unit))
                }
            ),
        );
    }
    pub fn build(mut self) -> FxHashMap<VarId, (Rc<str>, TypeScheme, Rc<runner::obj::Object>)> {
        self.def_int_functions();
        self.def_float_functions();
        self.def_bool_functions();
        self.def_str_functions();
        self.def_list_functions();
        self.def_unit_functions();
        self.def_func_functions();
        self.def_comma_functions();
        self.def_io_functions();
        self.funcs
    }
}
