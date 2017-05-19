module paper::lambda::base::Semantics

import paper::lambda::base::Syntax;
import paper::lambda::base::Resolve;
extend paper::ParseRedex; // parse bug
import String;


syntax E
  = "(" Value* E Expr* ")"
  | "(" "if0" E Expr Expr ")"
  | hole: Expr 
  ;
  
  
CR red("+", E e, (Expr)`(+ <Num n1> <Num n2>)`)
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("βv", E e, (Expr)`((λ (<Id x>) <Expr b>) <Value v>)`)
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

CR red("if0", E e, (Expr)`(if0 <Num n> <Expr then> <Expr els>`)
  = {<e, (Num)`0` := n ? then : els>};

default CR red(str _, E _, Tree _) = {};

R reduceLambdaV(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv"});

int toInt(Num x) = toInt("<x>");  
  
Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;
