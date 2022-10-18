module lang::credex::demo::amb::L


import lang::credex::demo::amb::Util;

extend lang::std::Layout;
extend lang::std::Id;


syntax Expr
  = bracket "(" Expr ")"
  | var: Id \ Reserved
  | amb: "amb" "{" Expr+ "}"
  | fix: "fix" Expr 
  | abs: "fun" Id ":" Type Expr
  > left add: Expr "+" Expr
  > right app: Expr Expr
  ;
  
  
syntax Type
  = "num"
  | right Type "-\>" Type
  ;
  
keyword Reserved
  = "num" | "amb" | "fix" | "if";
  
  
// Γ
syntax TEnv
  = "·" 
  | Id ":" Type TEnv
  ;
  
