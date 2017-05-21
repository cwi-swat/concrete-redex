module paper::r5rs::ToplevelAndVariables

import paper::r5rs::Syntax;
import paper::r5rs::Util;
import paper::ParseRedex;


CR red("5def", P p, (Def)`(define <Id x> <Value v>)`)
  = <p[store=add(x, v, p.store)], (Expr)`unspecified`>
  when x notin dom(p.store);
    
CR red("5redef", P p, (Def)`(define <Id x> <Value v>)`)
  = <p[store=update(x, v, p.store)], (Def)`unspecified`>
  when x in dom(p.store);

// NB: leaving d as reduct, which will be plugged D[Expr].
CR red("5tbegin", p:(P)`<Store s> ⊢ <DWS* dws> <D[Expr] _> <Defs* ds2>` , (Def)`(begin^D <Def d> <Def* ds1>)`)
  = <(P)`<Store s> ⊢ <DWS* dws> <D[Expr] _> <Defs* ds1> <Defs* ds2>`, d>; 
  
CR red("5tbegine", P p , (Def)`(begin^D)`)
  = <p, (Def)`unspecified`>;

// NB: moving d out of context, into reduct.  
CR red("5tdrop", p:(P)`<Store s> ⊢ <DWS* dws> <D[Expr] _> <Def d> <Defs* ds>` , (Def)`(#%values <Value* _>)`)
  = <(P)`<Store s> ⊢ <DWS* dws> <D[Expr] _> <Defs* ds>`, d>;
  
CR red("5var", P p, (Def)`<Id x>`)
  = <p, v>
  when 
    (Store)`<Value v>` := lookup(x, p.store);
  

CR red("5set", P p, (Def)`(set! <Id x> <Value v>)`)
 = <p[store=update(x, v, p.store)], (Def)`unspecified`>
 when x in dom(p.store);

 
set[str] toplevelAndVariables() = {"5def", "5redef", "5tbegin", "5tbegine", "5tdrop", "5var", "5set"};