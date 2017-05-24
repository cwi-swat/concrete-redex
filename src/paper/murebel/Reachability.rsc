module paper::murebel::Reachability

import paper::murebel::Context;
import paper::murebel::Syntax;
import util::Maybe;

// find heap addresses possibly modified by stmt
// assume there are no free vars in stmt

set[Ref] reachable(Stmt stmt, Store s, Spec spec) {
  set[Ref] refs = {};
  
  top-down-break visit(stmt) {
    case (Stmt)`let <Id x> = <Expr e> in <Stmt b>`: {
      if (just(Ref r) := eval(e, s)) {
        refs += reachable(subst((Expr)`<Id x>`, e, b), s, spec);
      }
    }
    case (Stmt)`<Expr e>.<Id x>(<{Expr ","}* args>);`: {
     if (just(Ref r) := eval(e, s)) { 
       refs += {r};
       Obj obj = lookup(r, store);
       if ((Value)`<Ref t>` := lookupField()) {
         // find state etc. do subst of args for formals
         // recurse on body 
         refs += reachable(body, s, spec);
       }
     }
    } 
    case (Stmt)`<Expr e>.<Id x> = <Expr _>;`: {
       refs += { r | just(Ref r) := eval(e, store) };
    } 
  }
  
  return refs;
}

Maybe[Ref] eval((Expr)`<Expr e>.<Id x>`, Store s) 
  = lookupField(lookup(r, s), x)
  when 
    just(Ref r) := eval(e, s);

Maybe[Ref] eval((Expr)`<Ref r>`, Store s) = just(r); 

default Maybe[Ref] eval(Expr _, Store _) = nothing();    
