module lang::credex::demo::lambda::state::Resolve

import lang::credex::Substitution;

import lang::credex::demo::lambda::state::Syntax;
extend lang::credex::demo::lambda::Resolve;

import ParseTree;
import IO;

/*
 * Extend resolve
 */
 
Refs resolve((Expr)`(set! <Id x> <Expr e>)`, list[Env] envs, Lookup lu) 
  = {<x@\loc,x,s,d> | <s,d> <- lu(x, x@\loc, envs)}
  + resolve(e, envs, lu);
  
Refs resolve((Expr)`(let ((<Id x> <Expr e>)) <Expr b>)`, list[Env] envs, Lookup lu) 
  = {<x@\loc, x, b@\loc, x@\loc>} // decls self-refer
  + resolve(e, envs, lu)
  + resolve(b, [{<b@\loc, x@\loc, x>}] + envs, lu);

// TODO: why do I need to repeat this?
// replace x with e in t
Expr subst(Expr x, Expr e, Expr t) = subst(#Expr, x, e, t, resolve);
