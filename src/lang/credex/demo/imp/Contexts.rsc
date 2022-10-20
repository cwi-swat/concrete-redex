module lang::credex::demo::imp::Contexts

extend lang::credex::demo::imp::Syntax;

syntax State = "[" {VarInt ","}* pairs "]";
syntax VarInt = Id "↦" Int;
syntax Conf = conf: State "⊢" Stmt;

syntax A
  = A "+" AExp
  | AExp "+" A
  | A "/" AExp
  | AExp "/" A
  | @hole Int "/" Int
  | @hole Int "+" Int
  | @hole Id
  ;

syntax B
  = A "\<=" AExp
  | Int "\<=" A 
  | "not" B
  | B "and" BExp
  | @hole Int "\<=" Int
  | @hole "not" Bool
  | @hole Bool "and" BExp
  ;

syntax S
  = Id ":=" A
  | seq: S!seq!seqSkip ";" Stmt
  | "if" B "then" Stmt "else" Stmt "fi"
  | @hole seqSkip: "skip" ";" Stmt
  | @hole "if" Bool "then" Stmt "else" Stmt "fi"
  | @hole "while" BExp "do" Stmt "od"
  | @hole Id ":=" Int
  ;
  
syntax C
  = State state "⊢" S
  ;  
