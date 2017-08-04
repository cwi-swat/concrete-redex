module paper::ContextExamples

import paper::ParseRedex;

// From: A Semantics for Context-Sensitive Reduction Semantics


// Fig 1
syntax A = "(" "+" A A ")" | Num;
syntax C = "(" "+" C A ")" | "(" "+" A C ")" | hole: A;


// Fig 3
syntax Expr = "(" Expr Expr ")" | Id | Value;
syntax Value = "(" "λ" "(" Id ")" Expr ")" | "+1" | Num;
syntax E = "(" E Expr ")" | "(" Value E ")" | hole: Expr;

  
// Fig 5 continuations

syntax Value = "call/cc" | "(" "cont" E ")";


// Fig 6 delimited continuations

syntax Expr = "(" "#" Expr ")";
syntax Value = "call/comp" | "(" "comp" M ")";


syntax M 
  = "(" M Expr ")" 
  | "(" Value M ")" 
  | hole: Expr
  ;
   
syntax EM // this is the unfolding of the notation E[(# M)]
  = "(" EM Expr ")" 
  | "(" Value EM ")" 
  | "(" "#" M ")"
  ;

syntax E = M | EM;


// Delimited
CR red("callcomp", E e, (Expr)`(call/comp <Value v>)`) 
  = {<e, (Expr)`(<Value v> (comp <M m>))`>}
  // can there be more than one? No because M has to have the hole 
  when /(EM)`(# <M m>)` := e; 


//CR red("callcomp", E[(Expr)`(# <M[(Expr)`(call/comp <Value v>)`]>)`]) 
//  = {<e, (Expr)`(<Value v> (comp <M m>))`>}
//  // can there be more than one? No because M has to have the hole 
//  when /(EM)`(# <M m>)` := e; 


// Callcc
CR red("callcc", E e, (Expr)`(call/cc <Value v>)`) = {<e, (Expr)`(<Value v> (cont <E e>))`>};
CR red("cont", E e, (Expr)`((cont <E e2>) <Value v>)`) = {<e2, (Expr)`<Value v>`>};


