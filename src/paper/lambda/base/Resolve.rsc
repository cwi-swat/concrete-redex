module paper::lambda::base::Resolve

import paper::lambda::Syntax;
import paper::Substitution;
import ParseTree;

Refs resolve((Expr)`(<Expr+ es>)`, list[Env] envs, Lookup lu)
  = ( {} | it + resolve(e, envs, lu) | Expr e <- es );

Refs resolve((Expr)`<Id x>`, list[Env] envs, Lookup lu)
  = {<x@\loc,x,s,d> | <s,d> <- lu(x, x@\loc, envs)};
  
Refs resolve((Expr)`(λ (<Id x>) <Expr e>)`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, e@\loc, x@\loc>} // decls self-refer
  + resolve(e, [{<e@\loc, x@\loc, x>}] + envs, lu);

default Refs resolve(Expr _, list[Env] _, Lookup _) = {};

// replace x with e in t
Expr subst(Expr x, Expr e, Expr t) = subst(#Expr, x, e, t, resolve);
