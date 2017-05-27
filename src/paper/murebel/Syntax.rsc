module paper::murebel::Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Prog
  = prog: Spec spec Stmt* stmts;

syntax Spec = spec: Entity* entities;

syntax Entity
  = entity: "entity" Id name "{" Field* fields State* states "}"
  ;

syntax Field
  = field: Id ":" Type
  ;
  
syntax Type
  = @category="Type" integer: "int"
  | @category="Type" string: "str"
  | @category="Type" boolean: "bool"
  | @category="Type" entity: Id \ Reserved
  ;

keyword Reserved = "int" | "str" | "bool";

syntax State
  = init: "init" Transitions transitions
  | final: "final" Id name ";"
  | state: "state" Id name Transitions transitions
  ;
  
syntax Transitions
  = single: Trans
  | many: "{" Trans* "}"
  ;
  
syntax Trans
  = trans: "on" Id name "(" {Formal ","}* formals ")" Goto? goto Pre? pre Stmt body
  ;
  
syntax Goto = ":" Id target;
syntax Pre = "require" Expr cond;
  
syntax Formal
  = formal: Id var ":" Type typ;  
  
syntax Stmt
  = block: "{" Stmt* "}"
  | \fail: "fail" ";"
  | assign: Expr "." Id "=" Expr ";" // todo: restrict to "this.x"
  | ifThen: "if" "(" Expr ")" Stmt () !>> "else" 
  | ifThenElse: "if" "(" Expr ")" Stmt "else" Stmt 
  | sync: "sync" Stmt
  | par: "par" Stmt 
  | skip: ";"
  | let: "let" Id "=" Expr "in" Stmt
  | trigger: Expr "." Id "(" {Expr ","}* ")" ";"
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
  | \value: Value
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