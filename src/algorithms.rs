// Algorithms.

use std::hash::{Hash,Hasher};
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{Debug, Error, Formatter};

// ===== Union Find =====

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

// ===== Tarjan's Strongly Connected Components =====

pub struct TRef<'a, T> {
	pub contents: &'a T,
}

impl<'a, T> TRef<'a, T> {
	pub fn from_ref(r: &'a T) -> TRef<'a, T> {
		TRef{
			contents: r,
		}
	}
}

// Why isn't #[derive(Clone)] sufficing to produce this implementation?
impl<'a, T> Clone for TRef<'a, T> {
	fn clone(&self) -> TRef<'a, T> {
		TRef{
			contents: self.contents,
		}
	}
}

impl<'a, T> Eq for TRef<'a, T> { }

impl<'a, T> PartialEq for TRef<'a, T> {
	fn eq(&self, other: &TRef<'a, T>) -> bool {
		(self.contents as *const T) == (other.contents as *const T)
	}
}

impl<'a, T> Hash for TRef<'a, T> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		(self.contents as *const T).hash(state);
	}
}

impl<'a, T> Debug for TRef<'a, T> {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		write!(fmt, "TRef({:?})", (self.contents as *const T))
	}
}

pub struct Dependencies<'a, T> {
	dependencies: HashMap<TRef<'a, T>, HashSet<TRef<'a, T>>>,
}

struct SCCState<'a, T> {
	result: Vec<Vec<TRef<'a, T>>>,
	index: HashMap<TRef<'a, T>, u64>,
	low_link: HashMap<TRef<'a, T>, u64>,
	on_stack: HashSet<TRef<'a, T>>,
	stack: Vec<TRef<'a, T>>,
	next_index: u64,
}

impl<'a, T: std::fmt::Debug> Dependencies<'a, T> {
	pub fn new() -> Dependencies<'a, T> {
		Dependencies{
			dependencies: HashMap::new(),
		}
	}

	pub fn add_vertex(&mut self, a: &'a T) {
		match self.dependencies.get_mut(&TRef::from_ref(a)) {
			None => { self.dependencies.insert(TRef::from_ref(a), HashSet::new()); },
			Some(_) => (),
		}
	}

	// Make a depend on b.
	pub fn add_dependency(&mut self, a: &'a T, b: &'a T) {
//		println!("Dep: {:?} -> {:?}", (a as *const _), (b as *const _));
//		println!("Dep: {:?} -> {:?}", a, b);
		self.add_vertex(a);
		self.add_vertex(b);
		// This unwrap is safe because of the above add_vertex(a).
		self.dependencies.get_mut(&TRef::from_ref(a)).unwrap().insert(TRef::from_ref(b));
	}

	fn strong_connect(&self, state: &mut SCCState<'a, T>, node: TRef<'a, T>) {
		state.index.insert(node.clone(), state.next_index);
		state.low_link.insert(node.clone(), state.next_index);
		state.next_index += 1;
		state.stack.push(node.clone());
		state.on_stack.insert(node.clone());

		if self.dependencies.contains_key(&node) {
			for dep in &self.dependencies[&node] {
				if !state.index.contains_key(dep) {
					self.strong_connect(state, dep.clone());
				} else if state.on_stack.contains(dep) {
					state.low_link.insert(
						node.clone(),
						std::cmp::min(state.low_link[&node], state.index[dep]),
					);
				}
			}
		}

		if state.low_link[&node] == state.index[&node] {
			let mut scc = Vec::<TRef<'a, T>>::new();
			loop {
				let w = state.stack.pop().unwrap();
				state.on_stack.remove(&w);
				// Save the flag before we move w away.
				let done_with_component = w == node;
				scc.push(w);
				if done_with_component {
					break;
				}
			}
			state.result.push(scc);
		}
	}

	pub fn strongly_connected_components(&self) -> Vec<Vec<TRef<'a, T>>> {
		let mut state = SCCState::<'a, T>{
			result: Vec::new(),
			index: HashMap::new(),
			low_link: HashMap::new(),
			on_stack: HashSet::new(),
			stack: Vec::new(),
			next_index: 0,
		};

		for node in self.dependencies.keys() {
			if !state.index.contains_key(&node) {
				self.strong_connect(&mut state, node.clone());
			}
		}

		state.result
	}
}

