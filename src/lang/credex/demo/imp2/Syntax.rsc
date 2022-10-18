module lang::credex::demo::imp2::Syntax

extend lang::std::Layout;
extend lang::std::Id;

syntax Pgm = "var" {Id ","}* ";" Stmt;

syntax Stmt
  = Id ":=" Expr
  | "skip"
  | Stmt ";" {Stmt ";"}+
  | "if" Expr "then" Stmt "else" Stmt "fi"
  | "while" Expr "do" Stmt "od";
 
syntax Expr
  = Int 
  | Id
  | Bool
  | "not" Expr
  > left div: Expr "/" Expr  
  > left add: Expr "+" Expr
  > non-assoc Expr "\<=" Expr
  > left Expr "and" Expr;
  
syntax Bool = "true" | "false";

lexical Int = [0-9]+ !>> [0-9];
  

