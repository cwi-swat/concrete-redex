module lang::credex::demo::lambda::Semantics

import lang::credex::demo::lambda::Syntax;
import lang::credex::demo::lambda::Resolve;
extend lang::credex::ParseRedex; // extend because parse bug
import String;

// Contexts
syntax E 
  = "(" Value* E Expr* ")" 
  | @hole "(" Value Value* ")"
  ;
  
CR red("+", E e, (E)`(+ <Num n1> <Num n2>)`)
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("βv", E e, (E)`((λ (<Id x>) <Expr b>) <Value v>)`)
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

default CR red(str _, E _, Tree _) = {};

R reduceLambdaV(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv"});

RR applyLambdaV(Expr e) = apply(#E, #Expr, red, e, {"+", "βv"});

TR traceLambdaV(Expr e, bool debug=false) = trace(applyLambdaV, e, debug=debug); 


int toInt(Num x) = toInt("<x>");  
  
Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;
