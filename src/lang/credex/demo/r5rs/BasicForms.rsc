module lang::credex::demo::r5rs::BasicForms

import lang::credex::demo::r5rs::Syntax;
import lang::credex::demo::r5rs::Util;
import lang::credex::ParseRedex;

// Fig 11. Basic syntactic forms

CR red("5if3t", P p, (Expr)`(if <Value v1> <Expr e1> <Expr e2>)`)
  = {<p, e1>}
  when (Value)`#f` !:= v1;
  

CR red("5if3f", P p, (Expr)`(if #f <Expr e1> <Expr e2>)`)
  = {<p, e2>};
  
CR red("5if2t", P p, (Expr)`(if <Value v1> <Expr e1>)`)
  = {<p, e1>}
  when (Value)`#f` !:= v1;
  

CR red("5if2f", P p, (Expr)`(if #f <Expr e1>)`)
  = {<p, (Expr)`unspecified`>};
  
CR red("5beginc", P p, (Expr)`(begin (#%values <Expr* vs>) <Expr+ es>)`)
  = {<p, (Expr)`(begin <Expr+ es>)`>}
  when allValue(vs);
  

CR red("5begin1", P p, (Expr)`(begin <Expr e1>)`)
  = {<p, e1>};

set[str] basicForms() = {"5if3t", "5if3f", "5if2t", "5if2f", "5beginc", "5begin1"};

