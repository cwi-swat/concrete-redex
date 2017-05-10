module lang::lambda::Semantics

import lang::lambda::Lambda;
extend credex::ConcreteRedex;
import credex::Substitution;
import String;
import IO;
import util::Maybe;

//(E (v ... E e ...) (if0 E e e) hole)
syntax E
  = "(" Value* E Expr* ")"
  | "(" "if0" E Expr Expr ")"
  | hole: Expr
  ;
        
CR rule("+", E e, (Expr)`(+ <Num n1> <Num n2>)`)
  = <e, [Expr]"<i1 + i2>">
  when 
    int i1 := toInt("<n1>"),
    int i2 := toInt("<n2>");

CR rule("if0f", E e, (Expr)`(if0 <Value v> <Expr e1> <Expr e2>)`)
  = <e, e2>
  when (Value)`0` !:= v;
  
CR rule("if0t", E e, (Expr)`(if0 0 <Expr e1> <Expr e2>)`)
  = <e, e1>;

CR rule("βv", E e, (Expr)`((λ (<Id* xs>) <Expr body>) <Expr* args>)`)
  = <e, newBody>
  when 
    allValue(args),
    list[Id] xl := [ x | Id x <- xs ],
    list[Expr] el := [ a | Expr a <- args ],
    size(xl) == size(el),
    Expr newBody := ( body | mySubst(it, (Expr)`<Id x>`, el[i]) | int i <- [0..size(xl)], Id x := xl[i] );
  
bool allValue(Expr* es) = ( true | it && (Expr)`<Value _>` := e | Expr e <- es );

Expr mySubst(Expr e, Expr x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, resolve);

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  Refs refs = {};
  top-down-break visit (exp) {
    case (Expr)`<Id x>`: 
      refs += { <x@\loc, x, scope, decl> | <loc scope, loc decl> <- lu(x, x@\loc, sc) };

    case (Expr)`(λ (<Id* xs>) <Expr e>)`: 
      refs += { <x@\loc, x, e@\loc, x@\loc> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<e@\loc, x@\loc, x> | Id x <- xs }, *sc], lu);
  }
  return refs;
}


Expr example() 
 = (Expr)`((λ (n) (if0 n 1 ((λ (x) (x x)) (λ (x) (x x))))) (+ 2 2))`;

Expr exampleWithFreeVars() 
 = (Expr)`(if0 n 1 ((λ (x) (x n)) n))`;
  
test bool simpleCapture()
  = (Expr)`(λ (x_) (+ x_ x))` := mySubst((Expr)`(λ (x) (+ x y))`, (Expr)`y`, (Expr)`x`);   
  
void runLambda(Expr e) = run(#Expr, #E, e, {"+", "if0f", "if0t", "βv"}); 





  
  