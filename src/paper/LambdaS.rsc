module paper::LambdaS

extend paper::LambdaV;
extend paper::Lambda;
extend paper::Credex;

syntax Expr // new expression constructs
  = "(" "let" "(" "(" Id Expr ")" ")" Expr ")"
  | "(" "set!" Id Expr ")";

keyword Reserved = "let";

// configurations
syntax Conf = Store "⊢" Expr; 

// configuration contexts
syntax C = Store store "⊢" E ctx; 

// stores
syntax Store = {VarVal ","}*;
syntax VarVal = Id "↦" Value;

syntax E // new expression evaluation contexts
  = "(" "let" "(" "(" Id E ")" ")" Expr ")"
  | "(" "set!" Id E ")";

CR red("var", C c, (Expr)`<Id x>`)
  = {<c, (Expr)`<Value v>`>}
  when Value v := lookup(c.store, x);

CR red("set", C c, (Expr)`(set! <Id x> <Value v>)`)
  = {<c[store=s], (Expr)`<Value v>`>}
  when Store s := update(c.store, x, v);

CR red("let", C c, 
  (Expr)`(let ((<Id x> <Value v>)) <Expr b>)`)
  = {<c[store=s], subst((Expr)`<Id x>`, (Expr)`<Id y>`, b)>}
  when 
    <Id y, _> := fresh(x, { var | /Id var := c.store }),
    Store s := update(c.store, y, v);

default CR red(str n, C c, Expr t)  // congruence
  = { <c, r> | Expr r <- ered(n, t) };
  
R reduceLambdaS(Conf c) = reduce(#C, #Conf, red, c, {"+", "βv", "var", "set", "let"});

/*
 * Lookup/update functions on store.
 */   
  
Value lookup((Store)`<{VarVal ","}* _>, <Id y> ↦ <Value v>, <{VarVal ","}* _>`, Id x) = v
  when x == y;
  
Store update((Store)`<{VarVal ","}* v1>, <Id y> ↦ <Value _>, <{VarVal ","}* v2>`, Id x, Value v)
  = (Store)`<{VarVal ","}* v1>, <Id x> ↦ <Value v>, <{VarVal ","}* v2>`
  when x == y;

default Store update((Store)`<{VarVal ","}* vs>`, Id x, Value v)
  = (Store)`<{VarVal ","}* vs>, <Id x> ↦ <Value v>`;

Conf letExample() = (Conf)` ⊢ (let ((x 3)) (set! x (+ x 1)))`;
Conf nestedLet() = (Conf)` ⊢ (let ((x 3)) (set! x (let ((x 10)) (+ x 1))))`;

  