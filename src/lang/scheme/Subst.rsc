module lang::scheme::Subst

import lang::scheme::Scheme;
import credex::Substitution;
import ParseTree;

Expr mySubst(Expr e, Id x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, subst, resolve, prime);

Id prime(Id x) = [Id]"<x>_";

//Refs refersTo((Expr)`<Id x>`, Lookup lu)
//  = { <x@\loc, def, x> | loc def <- lu(x, x@\loc) };
//  
//Refs refersTo((Expr)`(set! <Id x> <Expr e>)`, Lookup lu)
//  = { <x@\loc, def, x> | loc def <- lu(x, x@\loc) };
//  
//Defs defines((Expr)`(lambda (<Id* xs>) <Expr e>)`)
//  = { <x@\loc, x, e> | Id x <- xs };


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
  return top-down-break visit(e) {
    case (Expr)`<Id z>` => replace(#Expr, y)
      when z == x
    case t:(Expr)`(lambda (<Id* xs>) <Expr z>)` => t
      when x <- xs 
  }
}
