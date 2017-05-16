module paper::LambdaSResolve

import paper::LambdaS;
extend paper::LambdaResolve;

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
