module lang::javascript::Contexts

extend lang::javascript::S5;

/*
 * Contexts
 */
 
syntax EAE
  = "[" "class" ":" EPrime "," "extensible" ":" Expr "," "proto" ":" Expr "," "code" ":" Expr "," "primval" ":" Expr "]"
  | "[" "class" ":" Expr "," "extensible" ":" EPrime "," "proto" ":" Expr "," "code" ":" Expr "," "primval" ":" Expr "]"
  | "[" "class" ":" Expr "," "extensible" ":" Expr "," "proto" ":" EPrime "," "code" ":" Expr "," "primval" ":" Expr "]"
  | "[" "class" ":" Expr "," "extensible" ":" Expr "," "proto" ":" Expr "," "code" ":" EPrime "," "primval" ":" Expr "]"
  | "[" "class" ":" Expr "," "extensible" ":" Expr "," "proto" ":" Expr "," "code" ":" Expr "," "primval" ":" EPrim "]"
  ;
  
  
syntax EPE
  = "[" "config" ":" EPrime "," "enum" ":" Expr "," "value" ":" Expr "," "writable" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" EPrime "," "value" ":" Expr "," "writable" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" Expr "," "value" ":" EPrime "," "writable" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" Expr "," "value" ":" Expr "," "writable" ":" EPrime  "]"
  | "[" "config" ":" EPrime "," "enum" ":" Expr "," "get" ":" Expr "," "set" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" EPrime "," "get" ":" Expr "," "set" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" Expr "," "get" ":" EPrime "," "set" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" Expr "," "get" ":" Expr "," "set" ":" EPrime  "]"
  ;
  
syntax EPrime
  = hole: Expr!val
  | Op1 "(" EPrime ")"
  | Op2 "(" EPrime "," Expr ")"
  | Op2 "(" Value "," EPrim ")"
  | EPrime "[" "\<" O "\>" "]"
  | EPrime "[" "\<" O "\>" "=" Expr  "]"
  | Value "[" "\<" O "\>" "=" EPrime  "]"
  | EPrime "[" Expr "\<" A "\>" "]"
  | Value "[" EPrime "\<" A "\>" "=" Expr  "]"
  | Value "[" Value "\<" A "\>" "=" EPrime  "]"
  
  | EPrime "[" Expr "]*"  
  | Value "[" EPrime "]*"  
  | Value "[" Value "]*"
  
  | EPrime "[" "delete" Expr "]"  
  | Value "[" "delete" EPrime "]"  
    
  | EPrime "[" Expr "=" Expr "]*"
  | Value "[" EPrime "=" Expr "]*"
  | Value "[" Value "=" EPrime "]*"
  | Value "[" Value "=" Value "]*"

  | EPrime "(" {Expr ","}* ")"
  | Value "(" EPrime ")"
  | Value "(" EPrime "," {Expr ","}+ ")"
  | Value "(" {Value ","}+ "," EPrime ")"
  | Value "(" {Value ","}+ "," EPrime "," {Expr ","}+ ")"

  | EPrime ":=" Expr
  | Value ":=" EPrime

  | "throw" EPrime
  | "let" "(" Id "=" EPrime ")" Expr

  | EPrime ";" Expr
  | Value ";" EPrime
  | "if" "(" EPrime ")" "{" Expr "}" "else" "{" Expr "}"
  | "eval" "(" EPrime "," Expr ")"
  | "eval" "(" Value "," EPrime ")"
  | "{" AV {StrPV ","}+ "," Str ":" EPE  "}"
  | "{" AV "," Str ":" EPE "," {StrPE ","}+ "}"
  | "{" AV {StrPV ","}+ "," Str ":" EPE "," {StrPE ","}+ "}"
  | "props" "(" EPrime ")"
  ;
  
syntax E  
  = EPrime
  | "try" E "catch" Id Expr 
  | "try" E "finally" Expr 
  | "label" ":" Id E
  | "break" Id E
  // added to make parseable
  | "try" F "finally" Expr
  | "try" G "finally" Expr
  | "label" ":" Id G
  ;
  
syntax F
  = EPrime
  | "label" ":" Id F
  | "break" Id F
  ;
  
syntax G
  = EPrime
  | "try" G "catch" Expr
  ;