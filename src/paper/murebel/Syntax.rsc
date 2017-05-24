module paper::murebel::Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Prog
  = Spec spec Stmt* stmts;

syntax Spec = Entity* entities;

syntax Entity
  = "entity" Id name "{" Field* fields State* states "}"
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
  = "init" Transitions transitions
  | "final" Id name ";"
  | "state" Id name Transitions transitions
  ;
  
syntax Transitions
  = Trans
  | "{" Trans* "}"
  ;
  
syntax Trans
  = "on" Id name "(" {Formal ","}* formals ")" Goto? goto Pre? pre Stmt body
  ;
  
syntax Goto = ":" Id target;
syntax Pre = "require" Expr cond;
  
syntax Formal
  = Id var ":" Type typ;  
  
syntax Stmt
  = "{" Stmt* "}"
  | "fail" ";"
  | Expr "." Id "=" Expr ";"
  | "if" "(" Expr ")" Stmt () !>> "else" 
  | "if" "(" Expr ")" Stmt "else" Stmt 
  | "sync" Stmt
  | "par" Stmt 
  | ";"
  | "let" Id "=" Expr "in" Stmt
  // disallow any Expr hier except this.field (?)
  // then lock just fields of the current obj
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
  | "!" Expr
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