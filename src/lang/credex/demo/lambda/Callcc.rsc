module lang::credex::demo::lambda::Callcc

extend lang::credex::demo::lambda::Syntax;
import lang::credex::demo::lambda::Resolve;
extend lang::credex::demo::lambda::Semantics; 
import lang::credex::Substitution;

syntax Value = "call/cc";


//  E[(call/cc v)] = E[(v (lambda (x) E[x]))]
CR red("callcc", E e, (E)`(call/cc <Value v>)`)
  = {<e, (Expr)`(<Value v> (λ (<Id x>) <Expr cc>))`>}
  when
    Id x := fresh((Id)`x`, { x | /Id x := e }), 
    Expr cc := plug(#Expr, e, (Expr)`<Id x>`); 


RR applyLambdaCallcc(Expr e) = apply(#E, #Expr, red, e, {"+", "β", "callcc"});


Expr callccExample()
  = (Expr)`(+ 1 (call/cc (λ (k) (k 2))))`;

void redexStepsCC(Expr e) {
  println("<e>");
  redexStepsCC_(e);
}

void redexStepsCC_(Expr e, str indent = "") {
  //println("E: <e>");
  if ((Expr)`<Value _>` := e) {
    return;
  }

  RR rr = applyLambdaCallcc(e);
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(rr) - 1 ? last : other> ";
    
  for (<str rule, Expr sub> <- rr) {
    println("<indented("└─", "├─")><e> \u001b[34m─<rule>→\u001b[0m <sub>");
    redexStepsCC_(sub, indent = indented(" ", "│"));
    i += 1;
  }
}
  
