// AST

use std::collections::HashSet;
use std::fmt::{Debug, Error, Formatter};

pub fn concat_vecs<T>(x: Vec<T>, y: Vec<T>) -> Vec<T> {
	let mut result: Vec<T> = vec!{};
	for i in x {
		result.push(i);
	}
	for i in y {
		result.push(i);
	}
	result
}

pub struct CodeBlock {
	pub declarations: Vec<Declaration>,
}

#[derive(Clone)]
pub enum Declaration {
	LetDeclaration(Binder, Expr),
	InductiveDeclaration(String, ConstructorList),
	TypeInference(Expr),
}

#[derive(Clone)]
pub enum Expr {
	Var(String),
	Number(i64),
	Abs(Binder, Box<Expr>),
	App(Box<Expr>, Box<Expr>),
	LetIn(Binder, Box<Expr>, Box<Expr>),
	Match(Box<Expr>, Vec<MatchClause>),
//	ConstructorRef(String, String),
}

#[derive(Clone)]
pub struct BinderList {
	pub binders: Vec<Binder>,
}

#[derive(Clone)]
pub struct Binder {
	pub name: String,
	pub type_annot: Option<TypeExpr>,
}

#[derive(Eq, PartialEq, Hash, Clone)]
pub enum TypeExpr {
	Var(String),
	App(String, TypeArgsList),
}

#[derive(Eq, PartialEq, Hash, Clone)]
pub struct TypeArgsList {
	pub args: Vec<TypeExpr>,
}

#[derive(Clone)]
pub struct PolyType {
	pub binders: HashSet<String>,
	pub mono: TypeExpr,
}

#[derive(Clone)]
pub struct ConstructorList {
	pub constructors: Vec<Constructor>,
}

#[derive(Clone)]
pub struct Constructor {
	pub name: String,
	pub binders: BinderList,
}

#[derive(Clone)]
pub struct MatchClause {
	pub constructor_name: String,
	pub binders: BinderList,
	pub result: Expr,
}

// =================
// Define formatting
// =================

impl Debug for Declaration {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		use self::Declaration::*;
		match self {
			LetDeclaration(name, expr) => write!(fmt, "{:?} := {:?};", name, expr),
			InductiveDeclaration(name, constructor_list) => {
				write!(fmt, "inductive {} :=", name)?;
				for (i, item) in constructor_list.constructors.iter().enumerate() {
					write!(fmt, " {:?}", item)?;
					if i != constructor_list.constructors.len() - 1 {
						write!(fmt, " |")?;
					}
				}
				Ok(())
			}
			TypeInference(expr) => write!(fmt, "infer {:?};", expr),
		}
	}
}

impl Debug for Expr {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		use self::Expr::*;
		match self {
			Var(name) => write!(fmt, "{}", name),
			Number(value) => write!(fmt, "{:?}", value),
//			BinOp(e1, kind, e2) => write!(fmt, "({:?} {:?} {:?})", e1, kind, e2),
			Abs(binders, expr) => write!(fmt, "\\{:?} -> {:?}", binders, expr),
			App(fn_expr, args) => write!(fmt, "({:?} {:?})", fn_expr, args),
			LetIn(name, e1, e2) => write!(fmt, "let {:?} := {:?} in {:?}", name, e1, e2),
			Match(matchand, clauses) => {
				write!(fmt, "match {:?} with", matchand)?;
				for (i, item) in clauses.iter().enumerate() {
					write!(fmt, " {:?}", item)?;
					if i != clauses.len() - 1 {
						write!(fmt, " |")?;
					}
				}
				write!(fmt, "end")
			}
//			ConstructorRef(inductive_name, constructor_name) =>
//				write!(fmt, "{}::{}", inductive_name, constructor_name),
		}
	}
}

impl Debug for TypeExpr {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		use self::TypeExpr::*;
		match self {
			Var(name) => write!(fmt, "?{}", name),
			App(name, type_args) => write!(fmt, "{}<{:?}>", name, type_args),
		}
	}
}

// TODO: Can I use a trait to reduce this duplication here?
// It's currently pretty disgusting... :/

/*
impl Debug for ArgsList {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		for (i, item) in self.args.iter().enumerate() {
			write!(fmt, "{:?}", item);
			if i != self.args.len() - 1 {
				write!(fmt, ", ");
			}
		}
		Ok(())
	}
}
*/

impl Debug for CodeBlock {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		for (i, item) in self.declarations.iter().enumerate() {
			write!(fmt, "{:?}", item)?;
			if i != self.declarations.len() - 1 {
				write!(fmt, "\n")?;
			}
		}
		Ok(())
	}
}

impl Debug for TypeArgsList {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		for (i, item) in self.args.iter().enumerate() {
			write!(fmt, "{:?}", item)?;
			if i != self.args.len() - 1 {
				write!(fmt, ", ")?;
			}
		}
		Ok(())
	}
}


impl Debug for BinderList {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		for (i, item) in self.binders.iter().enumerate() {
			write!(fmt, " {:?}", item)?;
			if i != self.binders.len() - 1 {
				write!(fmt, ",")?;
			}
		}
		Ok(())
	}
}

impl Debug for Binder {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		match &self.type_annot {
			None => write!(fmt, "{}", self.name),
			Some(ty) => write!(fmt, "{} : {:?}", self.name, ty),
		}
	}
}

impl Debug for Constructor {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		write!(fmt, "{}{:?}", self.name, self.binders)
	}
}

impl Debug for MatchClause {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		write!(fmt, "{}{:?} => {:?}", self.constructor_name, self.binders, self.result)
	}
}

/*
impl Debug for BinOpKind {
	fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
		use self::BinOpKind::*;
		match self {
			Add => write!(fmt, "+"),
			Sub => write!(fmt, "-"),
			Mul => write!(fmt, "*"),
			Div => write!(fmt, "/"),
		}
	}
}
*/

