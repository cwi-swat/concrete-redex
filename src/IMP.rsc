module IMP

extend lang::std::Layout;
extend lang::std::Id;

syntax AExp
  = Int 
  | Id
  | left AExp "/" AExp  
  > left AExp "+" AExp
  ;
  
syntax BExp
  = Bool
  | "not" BExp
  | AExp "\<=" AExp
  | left BExp "and" BExp
  ;
  
syntax Stmt
  = Id ":=" AExp
  | "skip"
  | left Stmt ";" Stmt // no lists for now
  | "if" BExp "then" Stmt "else" Stmt "fi"
  | "while" BExp "do" Stmt "od"
  ;
 
 
syntax Pgm
  = "var" {Id ","}* ";" Stmt
  ;

lexical Bool
  = "true" | "false";

lexical Int
  = [0-9]+ !>> [0-9];
  
  
  