module lang::scheme::Subst

import lang::scheme::Scheme;
import credex::Substitution;
import ParseTree;
import util::Maybe;

Expr mySubst(Expr e, Expr x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, resolve);

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  Refs refs = {};
  top-down-break visit (exp) {
    case (Expr)`<Id x>`:
      refs += { <x@\loc, x, scope, def> | <loc scope, loc def> <- lu(x, x@\loc, sc) };
  
    case (Expr)`(set! <Id x> <Expr e>)`: 
      refs += { <x@\loc, x, scope, def> | <loc scope, loc def> <- lu(x, x@\loc, sc) }
        + resolve(e, sc, lu);
    
    case (Expr)`(letrec (<Binding* bs>) <Expr e>)`: {
      set[Id] xs = {};
      for ((Binding)`(<Id x> <Expr ex>)` <- bs) {
        refs += { <x@\loc, x, ex@\loc, x@\loc>, <x@\loc, x, e@\loc, x@\loc> }; // defs refer to themselves
        xs += {x};
        
      }
      for ((Binding)`(<Id _> <Expr ex>)` <- bs) {
        refs += resolve(ex,  [ {<ex@\loc, x@\loc, x> |  Id x <- xs }, *sc ], lu); 
      }
      refs += resolve(e, [ {<e@\loc, x@\loc, x> |  Id x <- xs }, *sc ], lu); 
    } 

    case (Expr)`(lambda (<Id* xs>) <Expr e>)`: 
      refs += { <x@\loc, x, e@\loc, x@\loc> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<e@\loc, x@\loc, x> | Id x <- xs }, *sc], lu);
  }
  return refs;
}

