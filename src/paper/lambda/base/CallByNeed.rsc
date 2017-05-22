module paper::lambda::base::CallByNeed

import paper::lambda::base::Syntax;
import paper::lambda::base::Resolve;
extend paper::ParseRedex; // extend because parse bug
import String;


syntax E 
  = hole: Expr
  | "(" "+" E Expr ")" 
  | "(" "+" Value E ")"
  | "(" E Expr ")"
  | "(" "(" "λ" "(" Id ")" E ")" Expr ")"
  | "(" "(" "λ" "(" Id ")" Ex ")" E ")"
  ;
  
syntax Ex 
  = Id // NB: not a hole!!
  | "(" "+" Ex Expr ")" 
  | "(" "+" Value Ex ")"
  | "(" Ex Expr ")"
  | "(" "(" "λ" "(" Id ")" Ex ")" Expr ")"
  ;

  
CR red("+", E e, (Expr)`(+ <Num n1> <Num n2>)`)
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("βv1", E e, (Expr)`((λ (<Id x>) <Value v>) <Expr _>)`)
  = {<e, (Expr)`<Value v>`>};

CR red("βv2", E e, (Expr)`((λ (<Id x>) <Expr b>) <Value v>)`)
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

default CR red(str _, E _, Tree _) = {};

R reduceLambdaCBN(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv1", "βv2"});

RR applyLambdaCBN(Expr e) = apply(#E, #Expr, red, e, {"+", "βv1", "βv2"});

int toInt(Num x) = toInt("<x>");  
  
Expr example1() 
 = (Expr)`((λ (x) (+ 1 1)) (+ 1 2))`;
 
Expr example2() 
 = (Expr)`((λ (x) (+ 1 x)) (+ 1 2))`;
 
 