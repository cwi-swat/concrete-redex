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

//NB: need tree here, because apply-red needs to accept multiple
// kinds of redexes.
CR red(str n, E c, Tree t)  // congruence
  = { <c, r> | Expr r <- ered(n, t) };

R applyRed(Expr e) = applyRed(#E, #Expr, red, e, {"+", "βv"});

private int toInt(Num x) = toInt("<x>");  
  
Refs resolve(Expr exp, list[Env] envs, Lookup lu) {
  Refs r = {};
  top-down-break visit (exp) {
    case (Expr)`<Id x>`: 
      r += {<x@\loc,x,s,d> | <s,d> <- lu(x, x@\loc, envs)};

    case (Expr)`(λ (<Id x>) <Expr e>)`: 
      r += {<x@\loc, x, e@\loc, x@\loc>} // decls self-refer
        + resolve(e, [{<e@\loc, x@\loc, x>}, *envs], lu);
  }
  return r;
}

Expr subst(Expr x, Expr e, Expr t) = subst(#Expr, x, e, t, resolve);

Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

