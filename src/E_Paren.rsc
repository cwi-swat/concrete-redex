module E_Paren





lexical Num =
  [0] 
  | [\-]? [1-9] [0-9]* 
  ;

layout Standard  =
  WhitespaceOrComment* !>> [\t-\a0D \  \u0205 \u0240 \U001680 \U00180E \U002000-\U00200A \U002028-\U002029 \U00202F \U00205F \U003000] !>> "//" 
  ;

syntax E =
  "\U0027E8" Expr  "*"  E "\U0027E9" 
  | "\U0027E8" "("  E  ")" "\U0027E9" 
  | @hole "\U0027E8" Num  "-"  Num "\U0027E9" 
  | @hole "\U0027E8" Num  "*"  Num "\U0027E9" 
  | "\U0027E8" Num  "-"  E "\U0027E9" 
  | @hole "\U0027E8" "("  Num  ")" "\U0027E9" 
  | "\U0027E8" E  "*"  Expr "\U0027E9" 
  | "\U0027E8" E  "-"  Expr "\U0027E9" 
  | "\U0027E8" Num "\U0027E9" 
  ;

syntax Expr =
  bracket "\U0027E8" "("  Expr  ")" "\U0027E9" 
  | "\U0027E8" Num "\U0027E9" 
  | left "\U0027E8" Expr  "*"  Expr "\U0027E9" 
  | left "\U0027E8" Expr  "-"  Expr "\U0027E9" 
  ;

lexical Whitespace =
  [\t-\a0D \  \u0205 \u0240 \U001680 \U00180E \U002000-\U00200A \U002028-\U002029 \U00202F \U00205F \U003000] 
  ;

lexical WhitespaceOrComment =
  whitespace: Whitespace 
  | comment: Comment 
  ;

lexical Comment =
  @lineComment @category="Comment" "//" ![\n]*$ 
  ;
