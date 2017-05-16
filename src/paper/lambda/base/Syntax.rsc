module paper::lambda::base::Syntax

extend lang::std::Layout;
extend lang::std::Id;

syntax Expr
  = var: Id \ Reserved | val: Value | apply: "(" Expr+ ")";

syntax Value
  = lambda: "(" "λ" "(" Id ")" Expr ")" | \num: Num | add: "+";

lexical Num = [0-9]+ !>> [0-9];

keyword Reserved = "λ";


