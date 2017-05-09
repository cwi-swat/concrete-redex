module lang::scheme::Subst

import lang::scheme::Scheme;
import credex::Substitution;
import ParseTree;

Expr mySubst(Expr e, Id x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, subst, resolve, prime);

Id prime(Id x) = [Id]"<x>_";

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  Refs refs = {};
  top-down-break visit (exp) {
    case (Expr)`<Id x>`:
      refs += { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) };
  
    case (Expr)`(set! <Id x> <Expr e>)`: 
      refs += { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) }
        + resolve(e, sc, lu);
        
    case (Expr)`(lambda (<Id* xs>) <Expr e>)`: 
      refs += { <x@\loc, x@\loc, x> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<x, x@\loc> | Id x <- xs }, *sc], lu);
  }
  return refs;
}

Expr subst(Expr e, Id x, Expr y) {
  return top-down-break visit(e) {
    case (Expr)`<Id z>` => replace(#Expr, y)
      when z == x
    case t:(Expr)`(lambda (<Id* xs>) <Expr z>)` => t
      when x <- xs 
  }
}
