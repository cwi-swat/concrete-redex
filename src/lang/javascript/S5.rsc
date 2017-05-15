module lang::javascript::S5

extend lang::std::Layout;
extend lang::std::Id;

syntax Ref = "@" Nat; // object references
syntax Loc = "#" Nat; // locations

syntax Value
  = "null"
  | "undefined"
  | Str
  | Num
  | "true"
  | "false"
  | Ref
  | "func" "(" {Id ","}* ")" "{" Expr "}"
  ; 

syntax Expr
  = val: Value
  | Id
  | Loc
  | "err" Value  
  | op1: Op1 "(" Expr ")"
  | op2: Op2 "(" Expr "," Expr ")"
  | Expr "[" "\<" O "\>" "]"
  | Expr "[" "\<" O "\>" "=" Expr  "]"
  | Expr "[" Expr "\<" A "\>" "]"
  | Expr "[" Expr "\<" A "\>" "=" Expr  "]"
  | Expr "[" Expr "]*"  
  | Expr "[" Expr "=" Expr "]*"
  | Expr "[" "delete" Expr "]"  
  | Expr "(" {Expr ","}* ")"
  > right Expr ":=" Expr
  | "label" ":" Id Expr
  | \break: "break" Id Expr
  | "throw" Expr
  | tryCatch: "try" Expr "catch" Id Expr 
  | tryFinally: "try" Expr "finally" Expr 
  | "let" "(" Id "=" Expr ")" Expr
  > left Expr ";" Expr
  | "if" "(" Expr ")" "{" Expr "}" "else" "{" Expr "}"
  | "eval" "(" Expr "," Expr ")"
  | "{" AE {StrPE ","}* "}"
  | "props" "(" Expr ")"
  ;

syntax O = "class" | "extensible" | "proto" | "code" | "primval";
  
syntax A = "writable" | "config" | "value" | "enum";

syntax AE
  = "[" "class" ":" Expr "," "extensible" ":" Expr "," "proto" ":" Expr "," "code" ":" Expr "," "primval" ":" Expr "]";

syntax AV
  = "[" "class" ":" Value "," "extensible" ":" Value "," "proto" ":" Value "," "code" ":" Value "," "primval" ":" Value "]";

syntax PE
  = "[" "config" ":" Expr "," "enum" ":" Expr "," "value" ":" Expr "," "writable" ":" Expr  "]"
  | "[" "config" ":" Expr "," "enum" ":" Expr "," "get" ":" Expr "," "set" ":" Expr  "]"
  ;
  
syntax PV
  = "[" "config" ":" Value "," "enum" ":" Value "," "value" ":" Value "," "writable" ":" Value  "]"
  | "[" "config" ":" Value "," "enum" ":" Value "," "get" ":" Value "," "set" ":" Value  "]"
  ;
  
syntax P = PV | "[" "]";

syntax Op1 = "string-\>num" | "typeof" | "log" | "prim-\>bool" ; // etc.

syntax Op2 = "string-append" | "+" | "/" | "*" | "-"; // etc.

// \theta
syntax Obj = "{" "[" AV "]" {StrPV ","}* "}";

// \sigma
syntax Store = {LocValue ","}*;

// \Theta
syntax Heap = {RefObj ","}*;

syntax LocValue = Loc ":" Value;
syntax RefObj = Ref ":" Obj;
syntax StrPV = Str ":" PV;
syntax StrPE = Str ":" PE;

lexical Str 
  = [\"] ![\"]* [\"];

lexical Nat = [0-9]+ !>> [0-9];

lexical Int = [\-]? Nat;

lexical Num 
  = Int !>> "."
  | Int "." Nat?
  ;

