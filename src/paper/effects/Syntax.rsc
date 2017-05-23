module paper::effects::Syntax

extend lang::std::Layout;
extend lang::std::Id;



syntax Value
   = var: Id \ Reserved
   | "true"
   | "false"
   | "fun" Pattern "↦" Computation
 //  | "rec" "fun" Pattern "↦" Computation
   | Handler
   | Num
   | Str
   | "(" ")"
   | "(" Value "," Value ")"
   | bracket "(" Value ")"
   | [\-+*/]
   ;

syntax Pattern
  = "_"
  | Id
  | "(" Pattern "," Pattern ")"
  | "(" ")"
  ;
  
lexical Num = [0-9]+ !>> [0-9];
lexical Str = [\"] ![\"]* [\"];
   
syntax Handler
  = "handler" "{" "return" Id x "↦" Computation cr "," {Clause ","}* clauses "}"
  ;
 
lexical Op
  =  Id "!";
  
syntax Clause
  = Op op "(" Pattern ";" Id ")" "↦" Computation;

syntax Computation
  = "return" Value
  | Op "(" Value ";" Id "." Computation ")"
  | Op Value  // sugar for (fun x -> op(x; y. return y)) v
  | right Computation ";" Computation // sugar
  > "do" Pattern "⟵" Computation "in" Computation
  | "if" Value "then" Computation "else" Computation
  | Value Value
  | "with" Value "handle" Computation
  | bracket "(" Computation ")"
  ; 
   
keyword Reserved
  = "true" | "false" | "fun" | "handler" | "do" | "in" | "if" 
  | "then" | "else" | "with" | "handle" | "return";