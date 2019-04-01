// Inference.

use std::hash::Hash;
use std::collections::HashMap;
use std::collections::HashSet;
use crate::ast;

pub struct UnionFindNode<T> {
	pub parent: u64,
	pub rank: u64,
	pub key: T,
}

pub struct UnionFind<T: Eq + Hash + Clone> {
	nodes: Vec<UnionFindNode<T>>,
	key_to_node_index: HashMap<T, u64>,
}

impl<T: Eq + Hash + Clone> UnionFind<T> {
	pub fn new() -> UnionFind<T> {
		UnionFind{
			nodes: vec!{},
			key_to_node_index: HashMap::new(),
		}
	}

	fn ensure_node(&mut self, x: &T) -> u64 {
		match self.key_to_node_index.get(&x) {
			Some(i) => return *i,
			_ => (),
		}
		if self.key_to_node_index.contains_key(&x) {
			return self.key_to_node_index[&x];
		}
		let new_node_index = self.nodes.len() as u64;
		self.key_to_node_index.insert(x.clone(), new_node_index);
		self.nodes.push(UnionFindNode{
			parent: new_node_index,
			rank: 0,
			key: x.clone(),
		});
		new_node_index
	}

	pub fn find(&mut self, x: &T) -> u64 {
		let xi = self.ensure_node(x);
		return self.find_by_index(xi);
	}

	fn find_by_index(&mut self, x: u64) -> u64 {
		let xi = x as usize;
		if self.nodes[xi].parent != x {
			let parent_value = self.nodes[xi].parent;
			self.nodes[xi].parent = self.find_by_index(parent_value);
		}
		self.nodes[xi].parent
	}

	pub fn canonicalize(&mut self, x: &T) -> T {
		let xi = self.find(x);
		return self.nodes[xi as usize].key.clone();
	}

	pub fn union(&mut self, x: &T, y: &T) {
		let xi = self.ensure_node(x);
		let yi = self.ensure_node(y);
		self.union_by_index(xi, yi);
	}

	fn union_by_index(&mut self, x: u64, y: u64) {
		let x_root_index = self.find_by_index(x);
		let y_root_index = self.find_by_index(y);
		let xi = x_root_index as usize;
		let yi = y_root_index as usize;
		if x_root_index == y_root_index {
			return;
		}
		if self.nodes[xi].rank < self.nodes[yi].rank {
			self.nodes[xi].parent = y_root_index;
		} else {
			self.nodes[yi].parent = x_root_index;
			if self.nodes[xi].rank == self.nodes[yi].rank {
				self.nodes[xi].rank += 1;
			}
		}
	}
}

pub struct UnificationContext {
	unions: UnionFind<ast::TypeExpr>,
	union_concrete_app: HashMap<ast::TypeExpr, ast::TypeExpr>,
}

impl UnificationContext {
	pub fn new() -> UnificationContext {
		UnificationContext{
			unions: UnionFind::new(),
			union_concrete_app: HashMap::new(),
		}
	}

	pub fn equate(&mut self, t1: &ast::TypeExpr, t2: &ast::TypeExpr) -> Result<(), String> {
//		println!("Equating: {:?} = {:?}", t1, t2);
		let t1 = self.unions.canonicalize(&t1);
		let t2 = self.unions.canonicalize(&t2);
//		println!("Canon:    {:?} = {:?}", t1, t2);

		self.unions.union(&t1, &t2);
//		for (t_index, t) in vec!{(t1_index, t1), (t2_index, t2)} {
		for t in &[&t1, &t2] {
			match t {
				ast::TypeExpr::Var(_) => (),
				ast::TypeExpr::App(_, _) => { self.union_concrete_app.insert((*t).clone(), (*t).clone()); }
			}
		}

		match (self.union_concrete_app.get(&t1), self.union_concrete_app.get(&t2)) {
			(
				Some(ast::TypeExpr::App(app1_name, app1_args)),
				Some(ast::TypeExpr::App(app2_name, app2_args)),
			) => {
				if app1_name != app2_name {
					return Err("Unification error".to_owned());
				}
				if app1_args.args.len() != app2_args.args.len() {
					return Err("Ill-formed unification".to_owned());
				}
				let sub_equates = app1_args.args.iter().zip(&app2_args.args)
					.map(|(x, y)| (x.clone(), y.clone())).collect::<Vec<_>>();
				for (a1, a2) in sub_equates {
					self.equate(&a1, &a2)?;
				}
			}
			_ => (),
		}

		for t in &[&t1, &t2] {
			match self.union_concrete_app.get(t) {
				Some(concretized_t) => {
					self.union_concrete_app.insert(
						self.unions.canonicalize(&t1),
						(*concretized_t).clone(),
					);
				}
				None => (),
			}
		}

		Ok(())
	}

	pub fn must_equal(&mut self, t1: &ast::TypeExpr, t2: &ast::TypeExpr) -> bool {
		return self.unions.find(&t1) == self.unions.find(&t2);
	}

	pub fn most_specific_type(&mut self, t: &ast::TypeExpr) -> ast::TypeExpr {
		let t_orig = t.clone();
		let mut t = self.unions.canonicalize(t);
		//t = self.unions.index_to_key(t_index).clone();
//		println!("Most specific: {:?} -> {:?} with {:?}", t_orig, t, self.union_concrete_app);
		match self.union_concrete_app.get(&t) {
			Some(concrete_t) => { t = (*concrete_t).clone(); }
			None => (),
		}
		match t {
			ast::TypeExpr::Var(_) => t,
			ast::TypeExpr::App(app_name, app_args) =>
				ast::TypeExpr::App(
					app_name.clone(),
					ast::TypeArgsList{
						args: app_args.args.iter().map(
							|t| self.most_specific_type(t)
						).collect(),
					}
				),
		}
	}
}

#[derive(Clone)]
pub struct Gamma {
	context: HashMap<String, ast::PolyType>,
	// The Declarations here are required to be ast::Declaration::InductiveDeclarations.
	inductives: HashMap<String, ast::Declaration>,
}

impl Gamma {
	pub fn new() -> Gamma {
		Gamma{
			context: HashMap::new(),
			inductives: HashMap::new(),
		}
	}

	pub fn lookup(&self, name: &String) -> Result<&ast::PolyType, String> {
		match self.context.get(name) {
			Some(x) => Ok(x),
			None => Err("Undefined variable: ".to_owned() + name),
		}
	}

	pub fn insert(&mut self, name: &String, t: ast::PolyType) {
		assert!(!self.context.contains_key(name));
		self.context.insert(name.clone(), t);
	}

	pub fn insert_inductive(&mut self, name: &String, decl: &ast::Declaration) {
		assert!(!self.inductives.contains_key(name));
		assert!(match decl { ast::Declaration::InductiveDeclaration(_, _) => true, _ => false });
		self.inductives.insert(name.clone(), decl.clone());
	}

	pub fn lookup_inductive(&self, name: &String) -> Result<&ast::Declaration, String> {
		match self.inductives.get(name) {
			Some(x) => Ok(x),
			None => Err("Undefined inductive: ".to_owned() + name),
		}
	}
}

// FIXME: Horrific time complexity.
pub fn free_type_variables(t: &ast::TypeExpr) -> HashSet<String> {
	let mut result = HashSet::<String>::new();
	match t {
		ast::TypeExpr::Var(name) => { result.insert(name.clone()); }
		ast::TypeExpr::App(_name, args) => {
			// TODO: What's the nice way of writing this?
			for arg in &args.args {
				for v in free_type_variables(&arg) {
					result.insert(v);
				}
			}
		}
	};
	result
}

pub struct InferenceContext {
	unification_context: UnificationContext,
	type_counter: u64,
}

fn apply_type_subs(subst: &HashMap<ast::TypeExpr, ast::TypeExpr>, t: &ast::TypeExpr) -> ast::TypeExpr {
	match subst.get(&t) {
		Some(t2) => t2.clone(),
		None => match t {
			ast::TypeExpr::App(app_name, app_args) =>
				ast::TypeExpr::App(
					app_name.clone(),
					ast::TypeArgsList{
						args: app_args.args.iter().map(|arg| apply_type_subs(&subst, &arg)).collect(),
					}
				),
			_ => t.clone(),
		}
	}
}

impl InferenceContext {
	pub fn new() -> InferenceContext {
		InferenceContext {
			unification_context: UnificationContext::new(),
			type_counter: 0,
		}
	}

	pub fn instantiate(&mut self, poly_t: &ast::PolyType) -> ast::TypeExpr {
		let mut subst = HashMap::<ast::TypeExpr, ast::TypeExpr>::new();
		for bound_variable in &poly_t.binders {
			subst.insert(ast::TypeExpr::Var(bound_variable.to_owned()), self.new_type());
		}
		apply_type_subs(&subst, &poly_t.mono)
	}

	pub fn new_type(&mut self) -> ast::TypeExpr {
		self.type_counter += 1;
		ast::TypeExpr::Var(self.type_counter.to_string())
	}

	pub fn new_poly_type(&mut self) -> ast::PolyType {
		ast::PolyType{
			binders: HashSet::new(),
			mono: self.new_type(),
		}
	}

	pub fn contextual_generalization(&self, gamma: &Gamma, t: &ast::TypeExpr) -> ast::PolyType {
		let mut all_bound = HashSet::<String>::new();
		for poly_t in gamma.context.values() {
			for v in &poly_t.binders {
				all_bound.insert(v.clone());
			}
		}
		ast::PolyType{
			binders: free_type_variables(t).difference(&all_bound).cloned().collect(),
			mono: t.clone(),
		}
	}

	pub fn infer(&mut self, gamma: &Gamma, t: &ast::Expr) -> Result<ast::TypeExpr, String> {
		match t {
			ast::Expr::Var(name) => Ok(self.instantiate(gamma.lookup(name)?)),
			ast::Expr::Number(_) => Err("No inference on numbers yet.".to_owned()),
			ast::Expr::Abs(binder, body) => {
				// This would be a great spot for either backtracking edits, or a persistent data structure.
				// FIXME: The current code results in quadratic time spent on duplicating contexts with nested abstractions.
				let mut gamma_prime = gamma.clone();
				let arg_type = self.new_type();
				let arg_poly_type = ast::PolyType{
					binders: HashSet::new(),
					mono: arg_type.clone(),
				};
				gamma_prime.insert(&binder.name, arg_poly_type);
				let result_type = self.infer(&gamma_prime, body)?;
				Ok(ast::TypeExpr::App(
					"fun".to_owned(), ast::TypeArgsList{args: vec!{arg_type, result_type}},
				))
			}
			ast::Expr::App(e1, e2) => {
				let fn_type = self.infer(gamma, e1)?;
				let arg_type = self.infer(gamma, e2)?;
				let result_type = self.new_type();
				self.unification_context.equate(
					&fn_type,
					&ast::TypeExpr::App(
						"fun".to_owned(), ast::TypeArgsList{args: vec!{arg_type, result_type.clone()}}
					),
				)?;
				Ok(result_type)
			}
			ast::Expr::LetIn(binder, e1, e2) => {
				let var_type = self.infer(gamma, e1)?;
				// FIXME: Check var_type against binder.type_annot.
				let var_type = self.unification_context.most_specific_type(&var_type);
				// This is where let-polymorphism is implemented.
				let var_poly_type = self.contextual_generalization(gamma, &var_type);
				let mut gamma_prime = gamma.clone();
				gamma_prime.insert(&binder.name, var_poly_type);
				self.infer(&gamma_prime, e2)
			}
			ast::Expr::Match(matchee, clauses) => {
				// First we infer a type for the matchee.
				let matchee_type = self.infer(&gamma, &matchee)?;

				// If we have no clauses then the matchee must be logically false.
				if clauses.is_empty() {
					let false_type = ast::TypeExpr::Var("False".to_owned());
					self.unification_context.equate(&matchee_type, &false_type)?;
					return Ok(false_type);
				}

				// Make up a new type.
				let result_type = self.new_type();
				let mut constructors_not_yet_covered: Option<HashSet<String>> = None;

				// Infer types for all of the clauses.
				for clause in clauses {
					// Get the inductive.
					let name_parts = clause.qualified_name.split("::").collect::<Vec<_>>();
					assert!(name_parts.len() == 2);
					let inductive_declaration = gamma.lookup_inductive(&name_parts[0].to_owned())?;

					match inductive_declaration {
						ast::Declaration::InductiveDeclaration(inductive_name, constructor_list) => {
							// If this is our first clause then fill in the constructors not yet covered.
							if constructors_not_yet_covered.is_none() {
								constructors_not_yet_covered = Some(
									constructor_list.constructors.iter().map(|c| c.name.clone()).collect(),
								);
							}
							// ... now remove the constructor we just covered.
							match &mut constructors_not_yet_covered {
								Some(set) => {
									if !set.contains(name_parts[1]) {
										return Err("Constructor used too many times in match clause: ".to_owned() + name_parts[1]);
									}
									set.remove(name_parts[1]);
								}
								None => (),
							}

							// Unify the matchee with this type.
							self.unification_context.equate(
								&matchee_type,
								&nulladic_app_type(inductive_name),
							)?;

							let mut gamma_prime = gamma.clone();
							let constructor_definition: &ast::Constructor =
								constructor_list.get_constructor(&name_parts[1].to_owned())?;
							let pairs = clause.binders.binders.iter().zip(
								constructor_definition.binders.binders.iter(),
							);
							for (local_binder, constructor_definition_binder) in pairs {
								//println!("  BINDER: {:?}  FOO: {:?}", binder, foo);
								// Ugh, why isn't this a reference appropriately?
								let mine = constructor_definition_binder.clone();
								gamma_prime.insert(
									&local_binder.name,
									ast::PolyType{
										binders: HashSet::new(),
										mono: mine.type_annot.unwrap().clone(),
									},
								);
							}

							let clause_type = self.infer(&gamma_prime, &clause.result)?;
							self.unification_context.equate(&result_type, &clause_type)?;
						}
						_ => panic!("BUG BUG BUG!"),
					}
				}
				// We must have consumed every constructor to be exhaustive.
				match constructors_not_yet_covered {
					Some(set) => {
						if !set.is_empty() {
							return Err(format!("Non-exhaustive match, missing: {:?}", set));
						}
					}
					None => (),
				}
				Ok(result_type)
			}
		}
	}
}

pub fn nulladic_app_type(s: &str) -> ast::TypeExpr {
	ast::TypeExpr::App(s.to_owned(), ast::TypeArgsList{args: vec!{}})
}

fn extract_sole_mono(t: &ast::PolyType) -> ast::TypeExpr {
	assert!(t.binders.is_empty());
	return t.mono.clone();
}

pub fn update_via_inference(ctx: &mut InferenceContext, gamma: &mut Gamma, block: &mut ast::CodeBlock) {
	// Add type annotations that we can know about.
	for declaration in &block.declarations {
		match declaration {
			ast::Declaration::LetDeclaration(binder, e) => {
				gamma.insert(&binder.name, ctx.new_poly_type());
			}
			ast::Declaration::InductiveDeclaration(name, constructor_list) => {
				gamma.insert_inductive(name, declaration);
				// The inductive itself has type Type.
				gamma.insert(
					name,
					ast::PolyType{
						binders: HashSet::new(),
						mono: nulladic_app_type("Type"),
					},
				);
				for constructor in &constructor_list.constructors {
					let mut constructor_type = nulladic_app_type(name);
					for binder in constructor.binders.binders.iter().rev() {
						let binder: &ast::Binder = binder;
						match &binder.type_annot {
							Some(constructor_argument_type) => {
								constructor_type = ast::TypeExpr::App(
									"fun".to_owned(),
									ast::TypeArgsList{
										args: vec!{
											constructor_argument_type.clone(),
											constructor_type,
										},
									},
								);
							}
							None => panic!("All inductive constructor arguments must have explicit types!"),
						}
					}
					let qualified_name = format!("{}::{}", name, constructor.name);
					gamma.insert(
						&qualified_name,
						ast::PolyType{
							binders: HashSet::new(),
							mono: constructor_type,
						},
					);
				}
			}
			ast::Declaration::TypeInference(_) => (),
		}
	}

	// Propagate everything we know.
	for declaration in &block.declarations {
		match declaration {
			ast::Declaration::LetDeclaration(binder, expr) => {
				let t = ctx.infer(gamma, expr).unwrap();
				let st = ctx.unification_context.most_specific_type(&t);
				// FIXME: Check the type annotation in binder against our inferred type.
				let decl_type = extract_sole_mono(gamma.lookup(&binder.name).unwrap());
				ctx.unification_context.equate(&decl_type, &st).unwrap();
			}
			_ => (),
		}
	}

	for declaration in &block.declarations {
		match declaration {
			ast::Declaration::TypeInference(expr) => {
				let t = ctx.infer(gamma, expr).unwrap();
				let st = ctx.unification_context.most_specific_type(&t);
				println!("Type inference: {:?} : {:?}", expr, st);
			}
			_ => (),
		}
	}
}

