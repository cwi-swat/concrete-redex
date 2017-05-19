module paper::ql::Syntax

extend lang::std::Layout;

start syntax Form
  = form: "form" Id name "{" Stm* body "}";
  
syntax Stm
  = question: Label label Id name ":" Type type
  | question: Label label Id name ":" Type type "=" Expr expr
  | ifThen: "if" "(" Expr cond ")" Stm!ifThen!ifThenElse
  | ifThenElse: "if" "(" Expr cond ")" Stm!ifThen!ifThenElse "else" Stm!ifThen!ifThenElse
  | block: "{" Stm* body "}" 
  ;

syntax Type
  = integer: "int"
  | boolean: "bool"
  | string: "str"
  ;  
  
syntax Value
  = strLit: Str
  | intLit: Int
  | boolLit: Bool
  ;

syntax Expr
  = var: Id name
  | val: Value
  | bracket "(" Expr ")"
  | not: "!" Expr
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
  | leq: Expr "\<=" Expr
  | lt: Expr "\<" Expr
  | eq: Expr "==" Expr
  | neq: Expr "!=" Expr
  )
  > left and: Expr "&&" Expr
  > or: Expr "||" Expr 
  ;
  
lexical Str
  = [\"]![\"]*[\"];
  
lexical Int
  = [1-9][0-9]* !>> [0-9];
  
syntax Bool
  = "true" | "false";

lexical Label
  = [\"]![\"]*[\"];
  
lexical Id
  = ([a-zA-Z][0-9a-zA-Z]* !>> [a-zA-Z0-9]) \ Reserved;
  
keyword Reserved
  = "true" | "false";