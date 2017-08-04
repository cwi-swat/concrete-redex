module lang::credex::demo::lambda::state::Syntax

extend lang::credex::demo::lambda::Syntax;

syntax Expr // new expression constructs
  = let: "(" "let" "(" "(" Id Expr ")" ")" Expr ")"
  | \set: "(" "set!" Id Expr ")";

keyword Reserved = "let";

