module paper::LambdaV

import paper::Lambda;

// extend, because reified grammar bug...
extend paper::Credex;
import String;
import IO;

// evaluation contexts
syntax E = "(" Value* E Expr* ")" | hole: Expr;

R ered("+", (Expr)`(+ <Num n1> <Num n2>)`)
  = {[Expr]"<toInt(n1) + toInt(n2)>"};

R ered("βv", (Expr)`((λ (<Id x>) <Expr b>) <Value e>)`)
  = {subst((Expr)`<Id x>`, (Expr)`<Value e>`, b)};

default R ered(str _, Expr _) = {};

// NB: need Tree for t here, because Credex::reduce needs
// to accept multiple kinds of redexes.
CR red(str n, E c, Tree t)  // congruence
  = { <c, r> | Expr r <- ered(n, t) };

R reduceLambdaV(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv"});

private int toInt(Num x) = toInt("<x>");  
  
Refs resolve((Expr)`(<Expr+ es>)`, list[Env] envs, Lookup lu)
  = ( {} | it + resolve(e, envs, lu) | Expr e <- es );

Refs resolve((Expr)`<Id x>`, list[Env] envs, Lookup lu)
  = {<x@\loc,x,s,d> | <s,d> <- lu(x, x@\loc, envs)};
  
Refs resolve((Expr)`(λ (<Id x>) <Expr e>)`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, e@\loc, x@\loc>} // decls self-refer
  + resolve(e, [{<e@\loc, x@\loc, x>}, *envs], lu);

default Refs resolve(Expr _, list[Env] _, Lookup _) = {};

// replace x with e in t
Expr subst(Expr x, Expr e, Expr t) = subst(#Expr, x, e, t, resolve);

Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;
