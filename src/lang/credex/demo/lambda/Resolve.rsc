module lang::credex::demo::lambda::Resolve

import lang::credex::demo::lambda::Syntax;
import lang::credex::Substitution;
import lang::credex::Resolve;
import IO;

void resolve((Expr)`<Id x>`, Resolver r) = r.refer(x);
  
void resolve(z:(Expr)`(λ (<Id x>) <Expr e>)`, Resolver r) {
  r.scope(e, () {
    r.declare(x);
    r.resolve(e);
  });
}

default void resolve(Expr e, Resolver r) {
  r.recurse(e);
} 
  

// replace x with e in t
Expr subst(Expr x, Expr e, Expr t) 
  = subst(#Expr, (x: e), t, resolve);
