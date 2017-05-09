module lang::lambda::Semantics

import lang::lambda::Lambda;
extend credex::ConcreteRedex;
import credex::Substitution;
import String;
import IO;

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
    Expr newBody := ( body | mySubst(it, xl[i], el[i]) | int i <- [0..size(xl)] );
  
bool allValue(Expr* es) = ( true | it && (Expr)`<Value _>` := e | Expr e <- es );

Expr mySubst(Expr e, Id x, Expr y)
  = substitute(#Expr, #Id, #Expr, e, x, y, subst, resolve, prime);

Id prime(Id x) = [Id]"<x>_";

Expr subst(Expr e, Id x, Expr y) {
  return top-down-break visit(e) {
    case (Expr)`<Id z>` => replace(#Expr, y)
      when z == x
    case t:(Expr)`(λ (<Id* xs>) <Expr z>)` => t
      when x <- xs 
  }
}

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  top-down-break visit (exp) {
    case (Expr)`<Id x>`:
      return { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) };
  
    case (Expr)`(λ (<Id* xs>) <Expr e>)`: 
      return { <x@\loc, x@\loc, x> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<x, x@\loc> | Id x <- xs }, *sc], lu);
  }
  return {};
}


Expr example() 
 = (Expr)`((λ (n) (if0 n 1 ((λ (x) (x x)) (λ (x) (x x))))) (+ 2 2))`;
  
void runLambda(Expr e) = run(#Expr, #E, e, {"+", "if0f", "if0t", "βv"}); 





  
  