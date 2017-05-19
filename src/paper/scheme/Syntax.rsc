module paper::scheme::Syntax

layout Standard 
  = Whitespace* !>> [\t\n\ ];

lexical Whitespace
  = [\ \t\n];

syntax Expr
  = "(" Expr Expr* ")"
  | "(" "set!" Id Expr ")"
  | "(" "begin" Expr+ ")"
  | "(" "if" Expr Expr Expr ")"
  | "(" "letrec" "(" Binding* ")" Expr ")"
  | Id //\ "begin" \ "if" \ "letrec" \ "lambda" \ "-"
  | Value
  ;

syntax Binding
  = "(" Id Expr ")"
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
  = ([a-zA-Z][0-9a-zA-Z_\-]* !>> [0-9a-zA-Z_\-]) \ "begin" \ "if" \ "-" \ "unspecified" \ "lambda" \ "letrec"
  ;