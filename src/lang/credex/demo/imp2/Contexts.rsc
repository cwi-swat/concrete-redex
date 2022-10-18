module lang::credex::demo::imp2::Contexts

extend lang::credex::demo::imp2::Syntax;
extend lang::credex::demo::imp2::State;

syntax C = State state "⊢" S;  

syntax S
  = Id ":=" E
  | S ";" {Stmt ";"}+
  | "if" E "then" Stmt "else" Stmt "fi"

  | @hole "skip" ";" {Stmt ";"}+
  | @hole "if" Bool "then" Stmt "else" Stmt "fi"
  | @hole "while" Expr "do" Stmt "od"
  | @hole Id ":=" Int
  ;
  

syntax E
  = E "+" Expr
  | Expr "+" E
  | E "/" Expr
  | Expr "/" E
  | E "\<=" Expr
  | Int "\<=" E 
  | "not" E
  | E "and" Expr
  
  | @hole Int "/" Int
  | @hole Int "+" Int
  | @hole Id
  | @hole Int "\<=" Int
  | @hole "not" Bool
  | @hole Bool "and" Expr
  ;

