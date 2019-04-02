// Main entry point.

#[macro_use] extern crate lalrpop_util;

use std::fs::File;
use std::io::Read;

mod ast;
mod inference;
mod algorithms;

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

//	normalize_to_whnf(&gamma,

//	uf.union(1, 2);
//	uf.union(3, 4);
//	uf.union(2, 3);


	Ok(())
}

