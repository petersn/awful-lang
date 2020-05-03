// Normalization.

use std::collections::HashMap;
use crate::ast;
use crate::inference;

type Name = i32;

#[derive(Debug, Clone)]
pub enum CompiledTerm {
    CompAbs {
        name: Name,
        body: Box<CompiledTerm>,
        free_vars: Vec<Name>,
    },
    RuntimeAbs {
        name: Name,
        body: Box<CompiledTerm>,
        closure: HashMap<Name, CompiledTerm>,
    },
    CompApp {
        fun: Box<CompiledTerm>,
        arg: Box<CompiledTerm>,
        arg_free_vars: Vec<Name>,
    },
    Thunk {
        body: Box<CompiledTerm>,
        closure: HashMap<Name, CompiledTerm>,
    },
    Var {
        name: Name,
    },
    Match {
        scrutinee: Box<CompiledTerm>,
        arms: Vec<()>,
    },
}

#[derive(Debug)]
pub struct CompiledBlock {
    pub name_string_table: Vec<String>,
    pub name_table: HashMap<String, Name>,
    pub root_context: HashMap<Name, CompiledTerm>,
}

impl CompiledBlock {
    pub fn new() -> CompiledBlock {
        CompiledBlock{
            name_string_table: vec!{},
            name_table: HashMap::new(),
            root_context: HashMap::new(),
        }
    }

    pub fn compile_term(&self, t: &ast::Expr) -> Result<CompiledTerm, String> {
        match t {
            ast::Expr::Var(s) => {
                Err("foo".to_owned())
            }
            _ => Err("foo".to_owned()),
        }
    }
    
    pub fn collect_name(&mut self, name: &str) {
        if !self.name_table.contains_key(name) {
            self.name_table.insert(name.to_owned(), self.name_string_table.len() as Name);
            self.name_string_table.push(name.to_owned());
        }
    }

    pub fn collect_names_from_binder(&mut self, binder: &ast::Binder) {
        self.collect_name(&binder.name);
        match &binder.type_annot {
            Some(type_expr) => self.collect_names_from_type_expr(&type_expr),
            None => (),
        }
    }

    pub fn collect_names_from_type_expr(&mut self, type_expr: &ast::TypeExpr) {
        match type_expr {
            ast::TypeExpr::Var(name) => self.collect_name(&name),
            ast::TypeExpr::App(name, args) => {
                self.collect_name(&name);
                for arg in &args.args {
                    self.collect_names_from_type_expr(&arg);
                }
            }
        }
    }

    pub fn collect_names_from_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Var(name) => self.collect_name(&name),
            ast::Expr::Number(_) => (),
            ast::Expr::Abs(binder, expr) => {
                self.collect_names_from_binder(binder);
                self.collect_names_from_expr(expr);
            }
            ast::Expr::App(fun, arg) => {
                self.collect_names_from_expr(fun);
                self.collect_names_from_expr(&arg);
            }
            ast::Expr::LetIn(binder, e1, e2) => {
                self.collect_names_from_binder(binder);
                self.collect_names_from_expr(e1);
                self.collect_names_from_expr(e2);
            }
            ast::Expr::Match(matchee, clauses) => {
                for clause in clauses {
                    self.collect_name(&clause.qualified_name);
                    for binder in &clause.binders.binders {
                        self.collect_names_from_binder(&binder);
                    }
                    self.collect_names_from_expr(&clause.result);
                }
            }
        }
    }

    pub fn get_free_vars(&self, expr: &ast::Expr) -> Vec<Name> {
        return inference::free_variables(expr).iter()
            .map(|name| self.name_table.get(name).unwrap()).copied().collect();
    }

    pub fn compile_expr(&mut self, expr: &ast::Expr) -> CompiledTerm {
        match &expr {
            ast::Expr::Var(name) => CompiledTerm::Var{ name: *self.name_table.get(name).unwrap() },
            ast::Expr::Number(_) => panic!("Number is current unhandled!"),
            ast::Expr::Abs(binder, expr) => {
                CompiledTerm::CompAbs{
                    name: *self.name_table.get(&binder.name).unwrap(),
                    body: Box::new(self.compile_expr(expr)),
                    free_vars: self.get_free_vars(expr),
                }
            }
            ast::Expr::App(fun, arg) => {
                CompiledTerm::CompApp{
                    fun: Box::new(self.compile_expr(fun)),
                    arg: Box::new(self.compile_expr(arg)),
                    arg_free_vars: self.get_free_vars(arg),
                }
            }
            ast::Expr::LetIn(binder, e1, e2) => {
                CompiledTerm::CompApp{
                    fun: Box::new(CompiledTerm::CompAbs{
                        name: *self.name_table.get(&binder.name).unwrap(),
                        body: Box::new(self.compile_expr(e2)),
                        free_vars: self.get_free_vars(e2),
                    }),
                    arg: Box::new(self.compile_expr(e1)),
                    arg_free_vars: self.get_free_vars(e1),
                }
            }
            ast::Expr::Match(matchee, clauses) => {
                Match{

                }
            }
            _ => panic!("Uh oh: {:?}", expr),
            /*
            ast::Expr::LetIn(binder, e1, e2) => {
                self.collect_names_from_binder(binder);
                self.collect_names_from_expr(e1);
                self.collect_names_from_expr(e2);
            }
            ast::Expr::Match(matchee, clauses) => {
                for clause in clauses {
                    self.collect_name(&clause.qualified_name);
                    for binder in &clause.binders.binders {
                        self.collect_names_from_binder(&binder);
                    }
                    self.collect_names_from_expr(&clause.result);
                }
            }
            */
        }
    }

    pub fn compile_block(&mut self, gamma: &inference::Gamma, block: &ast::CodeBlock) {
        // Collect all relevant strings.
        for declaration in &block.declarations {
            match &declaration {
                ast::Declaration::LetDeclaration(binder, expr) => {
                    self.collect_names_from_binder(&binder);
                    self.collect_names_from_expr(&expr);
                }
                ast::Declaration::InductiveDeclaration(name, constructor_list) => {
                    self.collect_name(&name);
                    for constructor in &constructor_list.constructors {
                        self.collect_name(&constructor.name);
                        for binder in &constructor.binders.binders {
                            self.collect_names_from_binder(&binder);
                        }
                    }
                }
                ast::Declaration::TypeInference(_) => {}
            }
        }
        println!("Names collected: {:?}", self.name_table);
        // Build each root declaration.
        for declaration in &block.declarations {
            match &declaration {
                ast::Declaration::LetDeclaration(binder, expr) => {
                    let decl_name = *self.name_table.get(&binder.name).unwrap();
                    let compiled_decl = self.compile_expr(expr);
                    self.root_context.insert(decl_name, compiled_decl);
                }
                _ => {}
            }
        }
    }
}

pub fn normalize_to_whnf(context: &HashMap<Name, CompiledTerm>, ct: CompiledTerm)
    -> Result<CompiledTerm, String>
{
    match ct {
        CompiledTerm::CompAbs{ name, body, free_vars } => {
            Ok(CompiledTerm::RuntimeAbs{
                name: name,
                body: body,
                closure: free_vars.iter().map(|v| (*v, context.get(v).unwrap().clone())).collect(),
            })
        }
        // FIXME: Is there something more idiomatic here? I can't write Ok(ct) because ct is moved out of.
        CompiledTerm::RuntimeAbs{ name, body, closure } => Ok(CompiledTerm::RuntimeAbs{ name, body, closure }),
        CompiledTerm::CompApp{ fun, arg, arg_free_vars } => {
            match normalize_to_whnf(context, *fun)? {
                CompiledTerm::RuntimeAbs{ name, body, mut closure } => {
                    closure.insert(name, if arg_free_vars.len() > 0 {
                        let arg_context: HashMap<Name, CompiledTerm> = arg_free_vars.iter()
                            .map(|v| (*v, context.get(v).unwrap().clone())).collect();
                        CompiledTerm::Thunk{
                            body: arg,
                            closure: arg_context,
                        }
                    } else {
                        *arg
                    });
                    return normalize_to_whnf(&closure, *body);
                }
                _ => return Err("CompApp's function's WHNF is not a RuntimeAbs somehow!".to_owned()),
            }
            Err("Whoops CompApp".to_owned())
        }
        CompiledTerm::Thunk{ body, closure } => normalize_to_whnf(&closure, *body),
        // XXX: Find something more efficient to do here than clone. Do I need Rc?
        CompiledTerm::Var{ name } => normalize_to_whnf(
            context, (*context.get(&name).unwrap()).clone(),
        ),
        _ => Err("Whoops.".to_owned()),
    }
}
