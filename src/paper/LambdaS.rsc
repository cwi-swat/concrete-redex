module paper::LambdaS

extend paper::Lambda;

syntax Expr // new expression constructs
  = let: "(" "let" "(" "(" Id Expr ")" ")" Expr ")"
  | \set: "(" "set!" Id Expr ")";

keyword Reserved = "let";

