module lang::credex::demo::lambda::Syntax

extend lang::std::Layout;
extend lang::std::Id;

syntax Expr 
  = var: Id \ Reserved 
  | val: Value 
  | app: "(" Expr+ ")";

syntax Value 
  = lam: "(" "λ" "(" Id ")" Expr ")" 
  | \num: Num 
  | add: "+";

lexical Num = [0-9]+ !>> [0-9];

keyword Reserved = "λ";


