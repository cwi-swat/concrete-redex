module paper::lambda::state::Semantics

import paper::lambda::base::Semantics;
import paper::lambda::state::Syntax;
import paper::lambda::state::Resolve;

import paper::MatchRedex; 
import paper::Substitution; // for fresh

// configurations
syntax Conf = conf: Store "⊢" Expr; 

// stores
syntax Store = {IdValue ","}*;
syntax IdValue = Id "↦" Value;

data E(loc src = |tmp:///|) // new expression evaluation contexts
  = let(Id, E, Expr)
  | \set(Id, E);
 
data C(loc src = |tmp:///|)
  = conf(Store store, E ctx);
  
CR red("var", C c:/hole((Expr)`<Id x>`))
  = {<c, (Expr)`<Value v>`>}
  when  isDefined(c.store, x), Value v := lookup(c.store, x);

CR red("set", C c:/hole((Expr)`(set! <Id x> <Value v>)`))
  = {<c[store=s], (Expr)`<Value v>`>}
  when isDefined(c.store, x), Store s := update(c.store, x, v);

CR red("let", C c:/hole((Expr)`(let ((<Id x> <Value v>)) <Expr b>)`))
  = {<c[store=s], subst((Expr)`<Id x>`, (Expr)`<Id y>`, b)>}
  when 
    Id y := fresh(x, { var | /Id var := c.store }),
    Store s := update(c.store, y, v);

default CR red(str n, C c:/E e1)  
  = { <plugCtx(c, e2), r> | <E e2, Expr r> <- red(n, e1) };
  
R reduceLambdaSA(Conf c) = reduce(#C, red, c, {"+", "βv", "var", "set", "let"}, #E);

/*
 * Lookup/update functions on store.
 */   

bool isDefined((Store)`<{IdValue ","}* _>, <Id y> ↦ <Value v>, <{IdValue ","}* _>`, Id x) = true
  when x == y;

default bool isDefined(Store _, Id _) = false;
  
Value lookup((Store)`<{IdValue ","}* _>, <Id y> ↦ <Value v>, <{IdValue ","}* _>`, Id x) = v
  when x == y;
  
Store update((Store)`<{IdValue ","}* v1>, <Id y> ↦ <Value _>, <{IdValue ","}* v2>`, Id x, Value v)
  = (Store)`<{IdValue ","}* v1>, <Id x> ↦ <Value v>, <{IdValue ","}* v2>`
  when x == y;

default Store update((Store)`<{IdValue ","}* vs>`, Id x, Value v)
  = (Store)`<{IdValue ","}* vs>, <Id x> ↦ <Value v>`;

Expr subst(Expr x, Expr e, Expr t) = subst(#Expr, x, e, t, resolve);


Conf xPlusX() = (Conf)`x ↦ 3 ⊢ (+ x x)`;

Conf letExample() = (Conf)` ⊢ (let ((x 3)) (set! x (+ x 1)))`;
Conf nestedLet() = (Conf)` ⊢ (let ((x 3)) (set! x (let ((x 10)) (+ x 1))))`;