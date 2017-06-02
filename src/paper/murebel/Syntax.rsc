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
  | assign: Expr "." Id "=" Expr ";" 
  | ifThen: "if" "(" Expr ")" Stmt () !>> "else" 
  | ifThenElse: "if" "(" Expr ")" Stmt "else" Stmt 
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
  = @category="Variable" var: Id \ "this" \ "true" \ "false"
  | new: "new" Id
  | \value: Value
  | this: "this"
  | field: Expr "." Id
  > not: "!" Expr
  > left ( 
    left mul: Expr "*" Expr
  | left div: Expr "/" Expr
  ) 
  > left ( 
    left add: Expr "+" Expr
  | left sub: Expr "-" Expr 
  )
  > non-assoc ( 
    gt: Expr "\>" Expr
  | geq: Expr "\>=" Expr 
  | lt: Expr "\<" Expr 
  | leq: Expr "\<=" Expr 
  | eq: Expr "==" Expr 
  | neq: Expr "!=" Expr
  | \in: Expr "in" Id
  )
  > left and: Expr "&&" Expr
  > left or: Expr "||" Expr
  | bracket \bracket: "(" Expr ")"
  ; 
  
  
lexical Num = [\-]?[0-9]+ !>> [0-9];  
  
