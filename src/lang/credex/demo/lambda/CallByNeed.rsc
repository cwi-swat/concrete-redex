module lang::credex::demo::lambda::CallByNeed

import lang::credex::demo::lambda::Syntax;
import lang::credex::demo::lambda::Resolve;
extend lang::credex::ParseRedex; // extend because parse bug
import String;


syntax E 
  = @hole "(" Value!lam Value* ")" // same as before
  | @hole "(" "(" "λ" "(" Id ")" Value ")" Expr ")"
  | @hole "(" "(" "λ" "(" Id ")" Expr ")" Value ")"
  | "(" Value!lam* E Expr* ")" // NB: !lam, because lambdas can reduce
  | "(" "(" "λ" "(" Id ")" E ")" Expr ")"
  | "(" "(" "λ" "(" Id ")" Ex ")" E ")"
  ;
  
syntax Ex 
  = Id // NB: not a hole!!
  | "(" Value!lam* Ex Expr* ")" 
  | "(" "(" "λ" "(" Id ")" Ex ")" Ex ")"
  ;

  
CR red("+", E e, (E)`(+ <Num n1> <Num n2>)`)
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("βv1", E e, (E)`((λ (<Id x>) <Value v>) <Expr _>)`)
  = {<e, (Expr)`<Value v>`>};

CR red("βv2", E e, (E)`((λ (<Id x>) <Expr b>) <Value v>)`)
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

default CR red(str _, E _, Tree _) = {};

R reduceLambdaCBN(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv1", "βv2"});

RR applyLambdaCBN(Expr e) = apply(#E, #Expr, red, e, {"+", "βv1", "βv2"});

int toInt(Num x) = toInt("<x>");  
  
Expr example1() 
 = (Expr)`((λ (x) (+ 1 1)) (+ 1 2))`;
 
Expr example2() 
 = (Expr)`((λ (x) (+ 1 x)) (+ 1 2))`;
 
 