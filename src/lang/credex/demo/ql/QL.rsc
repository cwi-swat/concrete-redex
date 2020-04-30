@license{
  Copyright (c) Tijs van der Storm <Centrum Wiskunde & Informatica>.
  All rights reserved.
  This file is licensed under the BSD 2-Clause License, which accompanies this project
  and is available under https://opensource.org/licenses/BSD-2-Clause.
}
@contributor{Tijs van der Storm - storm@cwi.nl - CWI}

module lang::credex::demo::ql::QL

extend lang::std::Layout;

start syntax Form
  = form: "form" Id name "{" Question* questions "}"
  ;

syntax Question
  = question: Label label Id var ":" Type type 
  | computed: Label label Id var ":" Type type "=" Expr expr
  | ifThen: "if" "(" Expr cond ")" Question () !>> "else"
  | ifThenElse: "if" "(" Expr cond ")" Question question "else" Question elseQuestion
  | @Foldable group: "{" Question* questions "}"
  | @Foldable @category="Comment" invisible: "(" Question* questions ")"
  ;

  
syntax Value
  = Integer
  | String
  | Bool
  ;
  
syntax Bool
  = "true"
  | "false"
  ;
  
syntax Expr
  = var: Id name
  | \value: Value
  | bracket "(" Expr ")"
  > not: "!" Expr
  > left (
      mul: Expr "*" Expr
    | div: Expr "/" Expr
  )
  > left (
      add: Expr "+" Expr
    | sub: Expr "-" Expr
  )
  > non-assoc (
      lt: Expr "\<" Expr
    | leq: Expr "\<=" Expr
    | gt: Expr "\>" Expr
    | geq: Expr "\>=" Expr
    | eq: Expr "==" Expr
    | neq: Expr "!=" Expr
  )
  > left and: Expr "&&" Expr
  > left or: Expr "||" Expr
  ;
  
keyword Keywords = "true" | "false" ;

lexical Label = @category="Constant" label: String; 
  
syntax Type
  = booleanType: "boolean" 
  | stringType: "string"
  | integerType: "integer"
  ;

lexical String = [\"] StrChar* [\"];

lexical StrChar
  = ![\"\\]
  | [\\][\\\"nfbtr]
  ;

lexical Integer =  [\-]? [0-9]+ !>> [0-9];
  
lexical Id 
  = ([a-z A-Z 0-9 _] !<< [a-z A-Z][\-a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Keywords
  ;
  
