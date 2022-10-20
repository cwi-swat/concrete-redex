module lang::credex::demo::lambda::Semantics

extend lang::credex::demo::lambda::Syntax;
import lang::credex::demo::lambda::Resolve;
extend lang::credex::ParseRedex; // extend because parse bug
import String;
import Set;
import IO;

// Contexts
syntax E 
  = "(" Value* E Expr* ")" 
  | @hole "(" Value Value* ")"
  ;
  
CR red("+", E e, (E)`(+ <Num n1> <Num n2>)`)
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("β", E e, (E)`((λ (<Id x>) <Expr b>) <Value v>)`)
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

default CR red(str _, E _, Tree _) = {};

R reduceLambdaV(Expr e) = reduce(#E, #Expr, red, e, {"+", "β"});

RR applyLambdaV(Expr e) = apply(#E, #Expr, red, e, {"+", "β"});

TR traceLambdaV(Expr e, bool debug=false) = trace(applyLambdaV, e, debug=debug); 


int toInt(Num x) = toInt("<x>");  
  
Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr bigger() = (Expr)`((λ (x) (+ x 2)) <Expr four>)`
  when Expr four := onePlusTwo();

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;

Expr avoidCaptureSmall() 
 = (Expr)`((λ (x) (λ (y) (+ y x))) (λ (z) y))`;

void redexSteps(Expr e) {
  println("<e>");
  redexSteps_(e);
}

void redexSteps_(Expr e, str indent = "") {
  //println("E: <e>");
  if ((Expr)`<Value _>` := e) {
    return;
  }

  RR rr = applyLambdaV(e);
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(rr) - 1 ? last : other> ";
    
  for (<str rule, Expr sub> <- rr) {
    println("<indented("└─", "├─")><e> \u001b[34m─<rule>→\u001b[0m <sub>");
    redexSteps_(sub, indent = indented(" ", "│"));
    i += 1;
  }
}
