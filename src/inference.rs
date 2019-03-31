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
			(Some(ast::TypeExpr::App(app1_name, app1_args)), Some(ast::TypeExpr::App(app2_name, app2_args))) => {
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

// FIXME: Horrific time complexity.
pub fn free_variables(t: &ast::Expr) -> HashSet<String> {
	let mut result = HashSet::<String>::new();
	match t {
		ast::Expr::Var(name) => { result.insert(name.clone()); }
		ast::Expr::Number(_) => (),
		ast::Expr::Abs(binder, e) => {
			let mut sub_vars = free_variables(&e);
			sub_vars.remove(&binder.name);
			for v in sub_vars {
				result.insert(v);
			}
		}
		ast::Expr::App(e1, e2) => {
			for e in &[&e1, &e2] {
				for v in free_variables(e) {
					result.insert(v);
				}
			}
		}
		ast::Expr::LetIn(binder, e1, e2) => {
			for v in free_variables(e1) {
				result.insert(v);
			}
			let mut sub_vars = free_variables(&e2);
			sub_vars.remove(&binder.name);
			for v in sub_vars {
				result.insert(v);
			}
		}
		ast::Expr::Match(matchee, clauses) => {
			for v in free_variables(matchee) {
				result.insert(v);
			}
			for clause in clauses {
				let mut sub_vars = free_variables(&clause.result);
				for binder in &clause.binders.binders {
					sub_vars.remove(&binder.name);
				}
				for v in sub_vars {
					result.insert(v);
				}
				// XXX: Do we include clause.constructor_name?
			}
		}
//		// XXX: Later if inductive definitions can have dependencies then this might have to change.
//		ast::Expr::ConstructorRef(_, _) => (),
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
			binders: HashSet::<_>::new(),
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
					binders: HashSet::<_>::new(),
					mono: arg_type.clone(),
				};
				gamma_prime.insert(&binder.name, arg_poly_type);
				let result_type = self.infer(&gamma_prime, body)?;
				Ok(ast::TypeExpr::App("fun".to_owned(), ast::TypeArgsList{args: vec!{arg_type, result_type}}))
			}
			ast::Expr::App(e1, e2) => {
				let fn_type = self.infer(gamma, e1)?;
				let arg_type = self.infer(gamma, e2)?;
				let result_type = self.new_type();
				self.unification_context.equate(
					&fn_type,
					&ast::TypeExpr::App("fun".to_owned(), ast::TypeArgsList{args: vec!{arg_type, result_type.clone()}}),
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
				// FIXME: All of this is horrifically broken.
				if clauses.is_empty() {
					return Ok(ast::TypeExpr::App("False".to_owned(), ast::TypeArgsList{args: vec!{}}));
				}
				// Make up a new type.
				let result_type = self.new_type();
				// Infer types for all of the clauses.
				for clause in clauses {
					// Define a context with the arguments of the constructor bound.
					let mut gamma_prime = gamma.clone();
					for binder in &clause.binders.binders {
						gamma_prime.insert(&binder.name, self.new_poly_type());
					}
					let clause_type = self.infer(&gamma_prime, &clause.result)?;
					self.unification_context.equate(&result_type, &clause_type)?;
				}
				Ok(result_type)
			}
//			ast::Expr::ConstructorRef(inductive_name, constructor_name) => {
//				// Look up the constructor.
//				Ok(self.new_type())
//			}
		}
	}
}

pub struct Dependencies {
	dependencies: HashMap<String, HashSet<String>>,
}

struct SCCState {
	result: Vec<Vec<String>>,
	index: HashMap<String, u64>,
	low_link: HashMap<String, u64>,
	on_stack: HashSet<String>,
	stack: Vec<String>,
	next_index: u64,
}

impl Dependencies {
	pub fn new() -> Dependencies {
		Dependencies{
			dependencies: HashMap::new(),
		}
	}

	// Make a depend on b.
	pub fn add_dependency(&mut self, a: &String, b: &String) {
		println!("Dep: {:?} -> {:?}", a, b);
		match self.dependencies.get_mut(a) {
			Some(dep_set) => { dep_set.insert(b.clone()); }
			None => {
				// TODO: Is there a better idiom here for a HashSet literal?
				let mut hs = HashSet::<_>::new();
				hs.insert(b.clone());
				self.dependencies.insert(a.clone(), hs);
			}
		}
	}

	fn strong_connect(&self, state: &mut SCCState, node: &String) {
		state.index.insert(node.clone(), state.next_index);
		state.low_link.insert(node.clone(), state.next_index);
		state.next_index += 1;
		state.stack.push(node.clone());
		state.on_stack.insert(node.clone());

		if self.dependencies.contains_key(node) {
			for dep in &self.dependencies[node] {
				if !state.index.contains_key(dep) {
					self.strong_connect(state, dep);
				} else if state.on_stack.contains(dep) {
					state.low_link.insert(node.clone(), std::cmp::min(state.low_link[node], state.index[dep]));
				}
			}
		}

		if state.low_link[node] == state.index[node] {
			let mut scc = Vec::<String>::new();
			loop {
				let w = state.stack.pop().unwrap();
				state.on_stack.remove(&w);
				// Save the flag before we move w away.
				let done_with_component = w == *node;
				scc.push(w);
				if done_with_component {
					break;
				}
			}
			state.result.push(scc);
		}
	}

	pub fn strongly_connected_components(&self) -> Vec<Vec<String>> {
		let mut state = SCCState{
			result: Vec::new(),
			index: HashMap::new(),
			low_link: HashMap::new(),
			on_stack: HashSet::new(),
			stack: Vec::new(),
			next_index: 0,
		};

		for node in self.dependencies.keys() {
			if !state.index.contains_key(node) {
				self.strong_connect(&mut state, node);
			}
		}

		state.result
	}
}

pub fn update_via_inference(ctx: &mut InferenceContext, gamma: &mut Gamma, block: &mut ast::CodeBlock) {
	let mut dependencies = Dependencies::new();
	let mut name_provided_by: HashMap<String, &ast::Declaration> = HashMap::new();

	// Determine what ast::Declarations provide which names, and what the dependencies are.
	for declaration in &block.declarations {
		match declaration {
			ast::Declaration::LetDeclaration(binder, e) => {
				for v in free_variables(e) {
					dependencies.add_dependency(&binder.name, &v);
				}
				name_provided_by.insert(binder.name.clone(), &declaration);
			}
			ast::Declaration::InductiveDeclaration(name, constructor_list) => {
				// XXX: I'm not entirely sure what to do here.
				name_provided_by.insert(name.clone(), &declaration);
				for constructor in &constructor_list.constructors {
					let qualified_name = format!("{}::{}", name, constructor.name);
					name_provided_by.insert(qualified_name, &declaration);
				}
			}
			ast::Declaration::TypeInference(expr) => (),
		}
	}

	let scc = dependencies.strongly_connected_components();
	println!("SCC: {:?}", scc);
	println!("Name provided by: {:?}", name_provided_by.keys());

	// FIXME: Add every other declaration that isn't in a component in scc at the end.

	// Perform inference for each connected component individually.
	for component in &scc {
		let mut name_types = HashMap::<String, ast::TypeExpr>::new();
		// Invent a fresh monotype for each name declared in this block.
		for name in component {
			let new_mono = ctx.new_type();
			name_types.insert(name.clone(), new_mono.clone());
			gamma.insert(
				name,
				ast::PolyType{
					binders: HashSet::<_>::new(),
					mono: new_mono.clone(),
				},
			);
		}
		// Infer each component in the block.
		for name in component {
			// Skip the names that no one provides, because they're currently inductives, or errors to be caught elsewhere.
			if !name_provided_by.contains_key(name) {
				continue;
			}
			let declaration: &ast::Declaration = name_provided_by[name];
			match declaration {
				ast::Declaration::LetDeclaration(binder, expr) => {
					let t = ctx.infer(gamma, expr).unwrap();
					let st = ctx.unification_context.most_specific_type(&t);
//					println!("BODY: {:?} : {:?}", expr, st);
					// FIXME: Check the type annotation in binder against our inferred type.
				}
				ast::Declaration::InductiveDeclaration(name, constructor_list) => {
					// XXX: Later I might need to do real inference here?

//					println!("TYPE NAMES: {:?} {}", name_types, name);

					// Mark the inductive itself as being of type Type.
					ctx.unification_context.equate(
						&name_types[name],
						&ast::TypeExpr::App("Type".to_owned(), ast::TypeArgsList{args: vec!{}}),
					).unwrap();

					//
				}
				ast::Declaration::TypeInference(expr) => (),
			}
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

