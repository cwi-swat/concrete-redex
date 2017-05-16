module paper::LambdaSA

extend paper::LambdaVA;
extend paper::Lambda;
extend paper::LambdaResolve;
import IO;

syntax Expr // new expression constructs
  = let: "(" "let" "(" "(" Id Expr ")" ")" Expr ")"
  | \set: "(" "set!" Id Expr ")";

keyword Reserved = "let";

// configurations
syntax Conf = conf: Store "⊢" Expr; 

// stores
syntax Store = {IdValue ","}*;
syntax IdValue = Id "↦" Value;

data E // new expression evaluation contexts
  = let(Id, E, Expr)
  | \set(Id, E);
 
data C(loc src = |tmp:///|)
  = conf(Store store, E ctx);
  
CR red("var", C c:/hole((Expr)`<Id x>`))
  = {<c, (Expr)`<Value v>`>}
  when isDefined(c.store, x), Value v := lookup(c.store, x);

CR red("set", C c:/hole((Expr)`(set! <Id x> <Value v>)`))
  = {<c[store=s], (Expr)`<Value v>`>}
  when isDefined(c.store, x), Store s := update(c.store, x, v);

CR red("let", C c:/hole((Expr)`(let ((<Id x> <Value v>)) <Expr b>)`))
  = {<c[store=s], subst((Expr)`<Id x>`, (Expr)`<Id y>`, b)>}
  when 
    Id y := fresh(x, { var | /Id var := c.store }),
    Store s := update(c.store, y, v);

default CR red(str n, C c:/E e)  
  = { <plugCtx(c, e2), r> | <E e2, Expr r> <- red(n, e),
    bprintln("C = <ctx2str(c)>"),
    bprintln("CTX: <ctx2str(e2)>, r = <r>"),
    bprintln("C[E[_]] = <ctx2str(plugCtx(c, e2))>")
     };
  
R reduceLambdaSA(Conf c) = reduce(#C, #Conf, red, c, {"+", "βv", "var", "set", "let"}, #E);


/*
 * Extend resolve
 */
 
Refs resolve((Expr)`(set! <Id x> <Expr e>)`, list[Env] envs, Lookup lu) 
  = {<x@\loc,x,s,d> | <s,d> <- lu(x, x@\loc, envs)}
  + resolve(e, envs, lu);
  
Refs resolve((Expr)`(let ((<Id x> <Expr e>)) <Expr b>)`, list[Env] envs, Lookup lu) 
  = {<x@\loc, x, b@\loc, x@\loc>} // decls self-refer
  + resolve(e, envs, lu)
  + resolve(b, [{<b@\loc, x@\loc, x>}] + envs, lu);
  
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

Conf letExample() = (Conf)` ⊢ (let ((x 3)) (set! x (+ x 1)))`;
Conf nestedLet() = (Conf)` ⊢ (let ((x 3)) (set! x (let ((x 10)) (+ x 1))))`;

  
  