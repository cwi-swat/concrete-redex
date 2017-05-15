module paper::LambdaV

import paper::Lambda;
import paper::LambdaResolve;

// extend, because reified grammar bug...
extend paper::Credex;
import String;
import IO;

// evaluation contexts
syntax E = "(" Value* E Expr* ")" | hole: Expr;

//syntax Expr = E "⟨" Expr redex "⟩";

R redE("+", (Expr)`(+ <Num n1> <Num n2>)`)
  = {[Expr]"<toInt(n1) + toInt(n2)>"};

R redE("βv", (Expr)`((λ (<Id x>) <Expr b>) <Value e>)`)
  = {subst((Expr)`<Id x>`, (Expr)`<Value e>`, b)};

default R redE(str _, Expr _) = {};

// NB: need Tree for t here, because Credex::reduce needs
// to accept multiple kinds of redexes.
default CR red(str n, E c, Tree t)  // congruence on E
  = { <c, r> | Expr r <- redE(n, t) };

R reduceLambdaV(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv"});

private int toInt(Num x) = toInt("<x>");  
  
Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;
