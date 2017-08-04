module lang::credex::demo::lambda::Callcc

extend lang::credex::demo::lambda::Syntax;
import lang::credex::demo::lambda::Resolve;
extend lang::credex::demo::lambda::Semantics; 
import lang::credex::Substitution;

syntax Value = "call/cc";


//  E[(call/cc v)] = E[(v (lambda (x) E[x]))]
CR red("callcc", E e, (Expr)`(call/cc <Value v>)`)
  = {<e, (Expr)`(<Value v> (λ (<Id x>) <Expr cc>))`>}
  when
    Id x := fresh((Id)`x`, { x | /Id x := e }), 
    Expr cc := plug(#Expr, e, (Expr)`<Id x>`); 

CR red("callcc", E e:/hole((Expr)`(call/cc <Value v>)`))
  = {<e, (Expr)`(<Value v> (λ (<Id x>) <Expr cc>))`>}
  when
    Id x := fresh((Id)`x`, { x | /Id x := e }), 
    Expr cc := plug(e, (Expr)`<Id x>`); 


RR applyLambdaCallcc(Expr e) = apply(#E, #Expr, red, e, {"+", "βv", "callcc"});


Expr callccExample()
  = (Expr)`(+ 1 (call/cc (λ (k) (k 2))))`;
  
