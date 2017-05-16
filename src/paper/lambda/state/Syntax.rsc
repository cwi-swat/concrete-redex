module paper::lambda::state::Syntax

extend paper::lambda::base::Syntax;

syntax Expr // new expression constructs
  = let: "(" "let" "(" "(" Id Expr ")" ")" Expr ")"
  | \set: "(" "set!" Id Expr ")";

keyword Reserved = "let";

