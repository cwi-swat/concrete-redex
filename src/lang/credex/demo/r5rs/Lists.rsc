module lang::credex::demo::r5rs::Lists

import lang::credex::demo::r5rs::Syntax;
import lang::credex::demo::r5rs::Util;
import lang::credex::ParseRedex;


CR red("5cons", P p, (Expr)`(#%cons <Value v1> <Value v2>)`)
  = {<p[store=s], (Expr)`<PP pp>`>}
  when 
    Store s := add(p.store, freshPP(p.store), (Stored)`(#%cons <Value v1> <Value v2>)`); 
    
CR red("5listc", P p, (Expr)`(#%list <Value v1> <Expr* vs>)`)
  = {<p, (Expr)`(#%cons <Value v1> (#%list <Expr* vs>))`>};
  
CR red("5listn", P p, (Expr)`(#%list)`)
  = {<p, (Expr)`#%null`>};
  
CR red("5car", P p, (Expr)`(#%car <PP pp>)`)
  = {<p, (Expr)`<Value v1>`>}
  when (Stored)`(#%cons <Value v1> <Value _>)` := lookup(pp, p.store);

CR red("5cdr", P p, (Expr)`(#%cdr <PP pp>)`)
  = {<p, (Expr)`<Value v2>`>}
  when (Stored)`(#%cons <Value _> <Value v2>)` := lookup(pp, p.store);

CR red("5null?t", P p, (Expr)`(#%null? #%null)`) = <p, (Expr)`#t`>;

CR red("5null?f", P p, (Expr)`(#%null? <Value v>)`) = <p, (Expr)`#f`>
  when (Value)`#%null` !:= v;
  
CR red("5pair?t", P p, (Expr)`(#%pair? <PP _>)`) = <p, (Expr)`#t`>;

CR red("5pair?f", P p, (Expr)`(#%pair? <Value v>)`) = <p, (Expr)`#f`>
  when (Value)`<PP _>` !:= v;

CR red("5setcar", P p, (Expr)`(#%set-car! <PP pp> <Value v>)`)
  = <p[store=s], (Expr)`unspecified`>
  when  
    (Stored)`(#%cons <Value _> <Value v2>)` := lookup(pp, p.store),
    Store s := update(pp, (Stored)`(#%cons <Value v> <Value v2>)`, p.store);
    
CR red("5setcdr", P p, (Expr)`(#%set-cdr! <PP pp> <Value v>)`)
  = <p[store=s], (Expr)`unspecified`>
  when  
    (Stored)`(#%cons <Value v1> <Value _>)` := lookup(pp, p.store),
    Store s := update(pp, (Stored)`(#%cons <Value v1> <Value v>)`, p.store);
  

set[str] lists() = {"5cons", "5listc", "5listn", "5car", "5cdr", "5null?t", "5null?f",
  "5pair?t", "5pair?f", "5setcar", "5setcdr"};