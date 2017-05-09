module lang::scheme::Subst

import lang::scheme::Scheme;
import credex::Substitution;
import ParseTree;
import util::Maybe;

Expr mySubst(Expr e, Id x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, subst, resolve, prime);

Id prime(Id x) = [Id]"<x>_";

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  Refs refs = {};
  top-down-break visit (exp) {
    case (Expr)`<Id x>`:
      refs += { <x@\loc, x, scope, def> | <loc scope, loc def> <- lu(x, x@\loc, sc) };
  
    case (Expr)`(set! <Id x> <Expr e>)`: 
      refs += { <x@\loc, x, scope, def> | <loc scope, loc def> <- lu(x, x@\loc, sc) }
        + resolve(e, sc, lu);
        
    case t:(Expr)`(lambda (<Id* xs>) <Expr e>)`: 
      refs += { <x@\loc, x, t@\loc, x@\loc> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<t@\loc, x@\loc, x> | Id x <- xs }, *sc], lu);
  }
  return refs;
}

Maybe[Expr] subst(Expr s, Id x, Expr e) {
  if ((Expr)`<Id z>` := s, z == x) {
    return just(e);
  }
  return nothing();
}
