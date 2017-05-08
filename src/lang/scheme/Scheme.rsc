module lang::scheme::Scheme

layout Standard 
  = Whitespace* !>> [\t\n\ ];

lexical Whitespace
  = [\ \t\n];

syntax Expr
  = "(" Expr Expr* ")"
  | "(" "set!" Id Expr ")"
  | "(" "begin" Expr+ ")"
  | "(" "if" Expr Expr Expr ")"
  | Id \ "begin" \ "if"
  | Value
  ;

syntax Value
  = "(" "lambda" "(" Id* ")" Expr ")"
  | Num
  | "#t"
  | "#f"
  | "-" !>> [0-9]
  | "unspecified"
  ;
  
lexical Num
  = [\-]?[0-9]+ !>> [0-9]
  ;

lexical Id
  = ([a-zA-Z][0-9a-zA-Z_\-]* !>> [0-9a-zA-Z_\-]) \ "begin" \ "if" \ "-" \ "unspecified" \ "lambda"
  ;