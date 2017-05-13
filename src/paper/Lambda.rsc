module paper::Lambda

extend lang::std::Layout;
extend lang::std::Id;

syntax Expr
  = Id \ Reserved | Value | "(" Expr+ ")";

syntax Value
  = "(" "λ" "(" Id ")" Expr ")" | Num | "+";

lexical Num = [0-9]+ !>> [0-9];

keyword Reserved = "λ";


