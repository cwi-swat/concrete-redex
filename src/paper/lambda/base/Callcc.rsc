module paper::lambda::base::Callcc

extend paper::lambda::base::Syntax;
import paper::lambda::base::Resolve;
extend paper::lambda::base::Semantics; 
import paper::Substitution;

syntax Value = "call/cc";


//  E[(call/cc v)] = E[(v (lambda (x) E[x]))]
CR red("callcc", E e, (Expr)`(call/cc <Value v>)`)
  = {<e, (Expr)`(<Value v> (λ (<Id x>) <Expr cc>))`>}
  when
    Id x := fresh((Id)`x`, { x | /Id y := e }), 
    Expr cc := plug(#Expr, e, (Expr)`<Id x>`); 


RR applyLambdaCallcc(Expr e) = apply(#E, #Expr, red, e, {"+", "βv", "callcc"});


Expr callccExample()
  = (Expr)`(+ 1 (call/cc (λ (k) (k 2))))`;
  
