module lang::scheme::Subst

import lang::scheme::Scheme;
import NameFix;
import ParseTree;

Expr mySubst(Expr e, Id x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, subst, resolve, prime);

Id prime(Id x) = [Id]"<x>_";

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  top-down-break visit (exp) {
    case (Expr)`<Id x>`:
      return { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) };
  
    case (Expr)`(set! <Id x> <Expr e>)`: 
      return { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) }
        + resolve(e, sc, lu);
        
    case t:(Expr)`(lambda (<Id* xs>) <Expr e>)`: 
      return { <x@\loc, x@\loc, x> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<x, x@\loc, t@\loc> | Id x <- xs }, *sc], lu);
  }
  return {};
}

Expr subst(Expr e, Id x, Expr y) {
  return visit(e) {
    case (Expr)`<Id z>` => y
      when z == x
  }
}
