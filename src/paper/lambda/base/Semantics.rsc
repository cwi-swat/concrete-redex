module paper::lambda::base::Semantics

import paper::lambda::base::Syntax;
import paper::lambda::base::Resolve;
import paper::MatchRedex;
import String;

data E(loc src = |tmp:///|) // evaluation contexts
  = apply(list[Value] done, E ctx, list[Expr] rest)
  | hole(Expr redex)
  ;
  
CR red("+", E e:/hole((Expr)`(+ <Num n1> <Num n2>)`))
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("βv", E e:/hole((Expr)`((λ (<Id x>) <Expr b>) <Value v>)`))
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

default CR red(str _, E _) = {};

R reduceLambdaVA(Expr e) = reduce(#E, red, e, {"+", "βv"});

int toInt(Num x) = toInt("<x>");  
  
Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;
