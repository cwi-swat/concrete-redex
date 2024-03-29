module lang::credex::demo::lambda::State

extend lang::credex::demo::lambda::Syntax;
extend lang::credex::demo::lambda::Semantics;
extend lang::credex::demo::lambda::Resolve;

extend lang::credex::ParseRedex; 
import lang::credex::Substitution; // for fresh

import ParseTree;
import IO;

syntax Expr // new expression constructs
  = let: "(" "let" "(" "(" Id Expr ")" ")" Expr ")"
  | \set: "(" "set!" Id Expr ")";

keyword Reserved = "let";

// configurations
syntax Conf = Store "⊢" Expr; 

// stores
syntax Store = {IdValue ","}*;
syntax IdValue = Id "↦" Value;

syntax E // new expression evaluation contexts
  = "(" "let" "(" "(" Id E ")" ")" Expr ")"
  | "(" "set!" Id E ")"
  | @hole Id \ Reserved
  | @hole "(" "set!" Id Value ")"
  | @hole "(" "let" "(" "(" Id Value ")" ")" Expr ")"
  ;

syntax C = Store store "⊢" E; 
  
  
CR red("var", C c, (E)`<Id x>`)
  = {<c, (Expr)`<Value v>`>}
  when  isDefined(c.store, x), Value v := lookup(c.store, x);

CR red("set", C c, (E)`(set! <Id x> <Value v>)`)
  = {<c[store=s], (Expr)`<Value v>`>}
  when isDefined(c.store, x), Store s := update(c.store, x, v);

CR red("let", C c, (E)`(let ((<Id x> <Value v>)) <Expr b>)`)
  = {<c[store=s], subst((Expr)`<Id x>`, (Expr)`<Id y>`, b)>}
  when 
    Id y := fresh(x, { var | /Id var := c.store }),
    Store s := update(c.store, y, v);

default CR red(str n, (C)`<Store s> ⊢ <E e1>`, Tree rx)  
  = { <(C)`<Store s> ⊢ <E e2>`, r> | <E e2, Expr r> <- red(n, e1, rx) };
  
R reduceLambdaS(Conf c) = reduce(#C, #Conf, red, c, {"+", "βv", "var", "set", "let"});
RR applyLambdaS(Conf c) = apply(#C, #Conf, red, c, {"+", "βv", "var", "set", "let"});
TR traceLambdaS(Conf c, bool debug=false) = trace(applyLambdaS, c, debug=debug);

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


/*
 * Extend resolve
 */
 
void resolve((Expr)`(set! <Id x> <Expr e>)`, Resolver r) {
  r.refer(x);
  r.resolve(e);
} 
  
void resolve(e:(Expr)`(let ((<Id x> <Expr e>)) <Expr b>)`, Resolver r) {
  r.resolve(e);
  r.scope(b, () {
    r.declare(x);
    r.resolve(b);
  });
} 

// TODO: why do I need to repeat this?
// replace x with e in t
Expr subst(Expr x, Expr e, Expr t) = subst(#Expr, x, e, t, resolve);

/*
 * Some example terms.
 */


Conf xPlusX() = (Conf)`x ↦ 3 ⊢ (+ x x)`;

Conf letExample() = (Conf)` ⊢ (let ((x 3)) (set! x (+ x 1)))`;
Conf nestedLet() = (Conf)` ⊢ (let ((x 3)) (set! x (let ((x 10)) (+ x 1))))`;

Conf bigLet() = (Conf)` ⊢ (let ((x 3)) (set! x (let ((x 10))
                      '     (+ x (let ((x 3)) (set! x (let ((x 10)) 
                      '      (+ x (let ((x 3)) (set! x (let ((x 10)) (+ x 1))))))))))))`;
