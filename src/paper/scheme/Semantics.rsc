module paper::scheme::Semantics

import paper::scheme::Syntax;
extend paper::ParseRedex;
import paper::scheme::Resolve;
import String;

syntax Store = "[" {VarValue ","}* "]";
syntax VarValue = Id "↦" Value;

syntax Conf = Store  "⊢" Expr;

syntax P = Store "⊢" E; 


syntax E 
  = hole: Expr //"[]"
  | "(" Expr* E Expr* ")"
  | "(" "set!" Id E ")"
  | "(" "begin" E Expr* ")"
  | "(" "if" E Expr Expr ")"
  ;


Conf paperExample() = (Conf)`[x ↦ 1] ⊢ ((set! x (- x)) (set! x (- x)))`;    

Expr lambda() = (Expr)`((lambda (x) (set! x y)) (lambda (z) y))`;  

RR applyScheme(Conf c) = apply(#P, #Conf, red, c, 
    {"MSet", "MLookup", "MSeq", "MTrivSeq", "MNeg", "MIfT", "MIfF"}); 


default CR red(str _, P _, Tree _) = {};

CR red("MApp", (P)`<Store s> ⊢ <E c>`, (Expr)`((lambda (<Id* xs>) <Expr e>) <Expr* es>)`)
  = <>
  when
    allValue(es);
  
CR red("MSet", (P)`<Store s> ⊢ <E e>`, (Expr)`(set! <Id x> <Value v>)`) 
  = {<(P)`<Store s2> ⊢ <E e>`, (Expr)`unspecified`>}
  when 
    isDefined(x, s),
    Store s2 := update(x, v, s);

CR red("MLookup", (P)`<Store s> ⊢ <E e>`, (Expr)`<Id x>`)  
  = {<(P)`<Store s> ⊢ <E e>`, (Expr)`<Value v>`>}
  when
    isDefined(x, s),
    Value v := lookup(x, s);

CR red("MSeq", P p, (Expr)`(begin <Value v> <Expr e> <Expr* erest>)`) 
  = {<p, (Expr)`(begin <Expr e> <Expr* erest>)`>};

CR red("MTrivSeq", P p, (Expr)`(begin <Expr e>)`) 
  = {<p, (Expr)`<Expr e>`>};

CR red("MIfT", P p, (Expr)`(if <Value v> <Expr e1> <Expr e2>)`) 
  = {<p, e1>}
  when (Value)`#f` !:= v;

CR red("MIfF", P p, (Expr)`(if #f <Expr e1> <Expr e2>)`) 
  = {<p, e2>};

CR red("MNeg", P p, (Expr)`(- <Num n>)`) 
  = {<p, [Expr]"<minN>">}
  when
    int minN := -toInt("<n>");

bool isDefined(Id x, (Store)`[<{VarValue ","}* _>, <Id y> ↦ <Value _>, <{VarValue ","}* _>]`) = true
  when x == y;
 
default bool isDefined(Id x, Store _) = false; 
  
Value lookup(Id x, (Store)`[<{VarValue ","}* _>, <Id y> ↦ <Value v>, <{VarValue ","}* _>]`) = v
  when x == y;
  
Store update(Id x, Value v, (Store)`[<{VarValue ","}* v1>, <Id y> ↦ <Value _>, <{VarValue ","}* v2>]`)
  = (Store)`[<{VarValue ","}* v1>, <Id x> ↦ <Value v>, <{VarValue ","}* v2>]`
  when x == y;
 
bool allValue(Expr* es) = ( true | it && (Expr)`<Value v>` := e | Expr e <- es );
 

