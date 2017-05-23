module paper::murebel::Contexts

extend paper::murebel::Syntax;

syntax Obj = Ref ":" Id class "[" St state "]"  "{" {Prop ","}* "}" ;

syntax St = "⊥" | Id;

syntax Value = Ref;

syntax Ref = "#" Num;  

syntax Prop = Id ":" Value ";";

syntax Store = Obj*;

syntax Lock = Id id "{" Obj* "}";
  
syntax Conf
  = Store store "," Lock* locks "⊢" Prog prog
  ;
  
syntax C = Store store "," Lock* locks "⊢" P prog;
  
syntax P = Spec spec Stmt* S Stmt*;

/*
  on f(): x require e S
  ===
  if (e) {
    to x {
      S
    }
  }
  else {
    fail;
  }

*/

syntax Stmt  
  = "onSuccess" "(" Ref "↦" Id ")" Stmt 
  | "sync" "(" Id lock ")" Stmt;
  
  
syntax S
  = hole: Stmt
  | "to" Id S
  | "{" Stmt* S Stmt* "}"
  | E "." Id "=" Expr ";"
  | Value "." Id "=" E ";"
  | "sync" "(" Id ")" S // NB: don't go into sync S
  | "let" Id "=" E "in" Stmt
  | E "." Id "(" {Expr ","}* ")" ";"
  | "if" "(" E ")" Stmt () !>> "else" 
  | "if" "(" E ")" Stmt "else" Stmt 
  | Value "." Id "(" E ")" ";"
  | Value "." Id "(" E "," {Expr ","}+ ")" ";"
  | Value "." Id "(" {Value ","}+ "," E "," {Expr ","}+ ")" ";"
  | Value "." Id "(" {Value ","}+ "," E ")" ";"
  ;

syntax E
  = hole: Expr
  | E "." Id
  | E "*" Expr
  | Value "*" E
  | E "/" Expr
  | Value "/" E
  | E "-" Expr
  | Value "-" E
  | E "+" Expr
  | Value "+" E
  | E "\>" Expr
  | Value "\>" E
  | E "\>=" Expr 
  | Value "\>=" E 
  | E "\<" Expr 
  | Value "\<" E 
  | E "\<=" Expr 
  | Value "\<=" E 
  | E "==" Expr 
  | Value "==" E 
  | E "!=" Expr
  | Value "!=" E
  ; 
