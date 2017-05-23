module paper::murebel::Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Prog
  = Spec Stmt*;

syntax Spec = Entity*;

syntax Entity
  = "entity" Id "{" Field* State* "}"
  ;

syntax Field
  = Id ":" Type
  ;
  
syntax Type
  = @category="Type" "int"
  | @category="Type" "str"
  | @category="Type" "bool"
  | @category="Type" Id \ Reserved
  ;

keyword Reserved = "int" | "str" | "bool";

syntax State
  = "init" Transitions
  | "final" Id ";"
  | "state" Id Transitions
  ;
  
syntax Transitions
  = Trans
  | "{" Trans* "}"
  ;
  
syntax Trans
  = "on" Id "(" {Formal ","}* ")" Goto? Pre? Stmt
  ;
  
syntax Goto = ":" Id;
syntax Pre = "require" Expr;
  
syntax Formal
  = Id ":" Type;  
  
syntax Stmt
  = "{" Stmt* "}"
  | "fail" ";"
  | Expr "." Id "=" Expr ";"
  | "if" "(" Expr ")" Stmt () !>> "else" 
  | "if" "(" Expr ")" Stmt "else" Stmt 
  | "sync" Stmt
  | ";"
  | "let" Id "=" Expr "in" Stmt
  | Expr "." Id "(" {Expr ","}* ")" ";"
  ;
  
syntax Value
  = @category="Constant" Num
  | Bool
  ;
  
lexical Bool = "true" | "false";  
  
syntax Expr
  = @category="Variable" Id \ "this" \ "true" \ "false"
  | "new" Id
  | Expr "." Id
  | Value
  | "this"
  > left ( 
    left Expr "*" Expr
  | left Expr "/" Expr
  ) 
  > left ( 
    left Expr "+" Expr
  | left Expr "-" Expr 
  )
  > non-assoc ( 
    Expr "\>" Expr
  | Expr "\>=" Expr 
  | Expr "\<" Expr 
  | Expr "\<=" Expr 
  | Expr "==" Expr 
  | Expr "!=" Expr
  )
  > left Expr "&&" Expr
  > left Expr "||" Expr
  ; 
  
  
lexical Num = [\-]?[0-9]+ !>> [0-9];  
  
/*

entity Account
 amount: int
 
 init 
   on open(initial) {
     amount = initial
     goto opened
   } 

 final closed
 
 state opened {
   on deposit(n) amount = amount + n;

   on withdraw(n) {
     check amount > n;
     amount = amount - n;
   }
   on close goto closed;
 }
end

entity Trans
  on init(x: int, from: Account, to: Account)
    sync {
      from.withDraw(x)
      to.deposit(x)
    }
    goto booked;

*/