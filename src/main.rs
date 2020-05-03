// Main entry point.

#[macro_use] extern crate lalrpop_util;

use std::collections::HashMap;
use std::fs::File;
use std::io::Read;

mod ast;
mod inference;
mod algorithms;
mod normalization;

lalrpop_mod!(pub grammar); // synthesized by LALRPOP

fn main() -> Result<(), std::io::Error> {
	let args: Vec<_> = std::env::args().collect();
	let mut file = File::open(&args[1])?;
	let mut contents = String::new();
	file.read_to_string(&mut contents)?;
	let mut ast = grammar::CodeBlockParser::new().parse(&contents).unwrap();
	println!("{:?}\n", ast);

//	let mut uf = inference::UnionFind::<i32>::new();

	let mut ctx = inference::InferenceContext::new();
	let mut gamma = inference::Gamma::new();
	inference::update_via_inference(&mut ctx, &mut gamma, &mut ast);
//	let f = ctx.infer(&gamma, ast).unwrap();
//	println!("\nPost inference:\n\n{:?}", ast);

	/*
	let mut scope: HashMap<String, &ast::Expr> = HashMap::new();
	for declaration in &ast.declarations {
		match declaration {
			ast::Declaration::LetDeclaration(binder, e) => {
				scope.insert(binder.name.clone(), e);
			}
			_ => {}
		}
	}
	*/

	//let main = gamma.lookup_definition(&"main".to_owned()).unwrap();
	//let main = scope.get("main").unwrap();
	let mut compiled_block = normalization::CompiledBlock::new();
	compiled_block.compile_block(&gamma, &ast);
	let main = compiled_block.root_context.get(
		compiled_block.name_table.get("main").unwrap(),
	).unwrap();
	println!("Main: {:?}", main);
	//println!("Name table: {:?}", compiled_block.name_table);
	let result = normalization::normalize_to_whnf(&compiled_block.root_context, main.clone());
	println!("Normalization: {:?}\n", result);

//	normalize_to_whnf(&gamma,

//	uf.union(1, 2);
//	uf.union(3, 4);
//	uf.union(2, 3);

	Ok(())
}
