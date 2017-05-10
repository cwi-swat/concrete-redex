module lang::imp::IMP

extend lang::std::Layout;
extend lang::std::Id;

syntax AExp
  = Int 
  | Id
  | left div: AExp "/" AExp  
  > left add: AExp "+" AExp
  ;
  
syntax BExp
  = Bool
  | not: "not" BExp
  | leq: AExp "\<=" AExp
  | left and: BExp "and" BExp
  ;
  
lexical Bool
  = "true" | "false";

syntax Int
  = Int_
  ;
  
lexical Int_
  = [0-9]+ !>> [0-9];
  

syntax Stmt
  = assign: Id ":=" AExp
  | "skip"
  | left seq: Stmt ";" Stmt // no lists for now
  | ite: "if" BExp "then" Stmt "else" Stmt "fi"
  | "while" BExp "do" Stmt "od"
  ;
 
 
syntax Pgm
  = "var" {Id ","}* ";" Stmt
  ;
