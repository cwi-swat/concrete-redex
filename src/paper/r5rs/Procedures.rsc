module paper::r5rs::Procedures

import paper::r5rs::Syntax;
import paper::r5rs::Util;
import paper::ParseRedex;


CR red("5calloc", P p, (Expr)`(lambda (<Id* xs>) <Expr+ es>)`)
  = {<p[store=add(cp, (Stored)`(lambda (<Id* xs>) <Expr+ es>)`, p.store)], (Expr)`<CP cp>`>}
  when CP cp := freshCP(p.store);

  
  
CR red("5μcalloc", P p, (Expr)`(lambda (<Id+ xs> . <Id xr>) <Expr+ es>)`)
  = {<p[store=s3], (Expr)`<MP mp>`>}
  when 
    MP mp := freshMP(p.store), CP cp := freshCP(p.store),
    Expr* ys := ids2exprs([ x | Id x <- xs ] + [xr]),
    Store s2 := add((Key)`<MP mp>`, (Stored)`(lambda (<Id+ xs> . <Id xr>) (<CP cp> <Expr* ys>))`, p.store),
    Store s3 := add((Key)`<CP cp>`, (Stored)`(lambda (<Id+ xs> <Id xr>) <Expr+ es>)`, s2);


CR red("5μcalloc1", P p, (Expr)`(lambda <Id x> <Expr+ es>)`)
  = {<p[store=s3], (Expr)`<MP mp>`>}
  when 
    MP mp := freshMP(p.store), CP cp := freshCP(p.store),
    Store s2 := add((Key)`<MP mp>`, (Stored)`(lambda <Id x> (<CP cp> <Id x>))`, p.store),
    Store s3 := add((Key)`<CP cp>`, (Stored)`(lambda (<Id x>) <Expr+ es>)`, s2);


CR red("5mark", P p, (Expr)`(<Expr* es1> <Expr e> <Expr* es2>)`)
  = {<p, (Expr)`(<Expr* es1> <Expr e>⬦ <Expr* es2>)`>}
  when
    (Expr)`<Value _>` !:= e, 
    ((Expr)`(lambda () <Expr+ _>)` := e && Expr call <- es1)
     ==> (Expr)`#%call-with-values` !:= call;

CR red("5unmark", P p, (Expr)`(<Expr* es1> <Value v>⬦ <Expr* es2>)`)
  = {<p, (Expr)`(<Expr* es1> <Value v> <Expr* es2>)`>};

CR red("5app", P p, (Expr)`(<CP cp> <Expr* es>)`)
  = {<p[store=s], reduct>}
  when
    allValue(es), // todo: isdefined
    (Stored)`(lambda (<Id* xs>) <Expr+ es>)` := lookup(cp, p.store),
    list[Id] xl := [ x | Id x <- xs ],
    size(xl) == size([ e | Expr e <- es ]), 
    Id* ys := fresh(xs, p.store),
    list[Id] yl := [ y | Id y <- ys ],
    Store s := ( p.store | add((Key)`<Id y>`, (Stored)`<Value v>`, it) | (Expr)`<Value v>` <- es ),
    Expr reduct := ( (Expr)`(begin <Expr+ es>)` | subst((Expr)`<Id x>`, (Expr)`<Id y>`, it) 
                       | i <- [0..size(xl)], Id x := xl[i], Id y := yl[i] ) 
    ;
    
CR red("5μapp", P p, (Expr)`(<MP mp> <Expr* es>)`)
  = {<p, (Expr)`(<CP cp> <Expr* args> (#%list <Expr* rest>))`>}
  when
    allValue(es),
    (Stored)`(lambda (<Id* xs> . <Id xr>) (<CP cp> <Expr* exs>))` := lookup(mp, p.store),
    list[Id] ys := [ y | Id y <- exs ],
    list[Expr] allArgs := [ e | Expr e <- es ],
    size(allArgs) == size(ys) + 1,
    Expr* args := exprs2exprStar(allArgs[0..-1]),
    Expr* rest := exprs2exprStar([allArgs[-1]]);

CR red("5μapp1", P p, (Expr)`(<MP mp> <Expr* es>)`)
  = {<p, (Expr)`(<CP cp> (#%list <Expr* es>))`>}
  when
    allValue(es),
    (Stored)`(lambda <Id x> (<CP cp> <Id x>))` := lookup(mp, p.store);
    
CR red("5applyc", P p, (Expr)`(#%apply <Fun1 f> <Expr* es> <PP pp>)`)
  = {<p, (Expr)`(#%apply <Fun1 f> <Expr* es> <Value v1> <Value v2>)`>}
  when
    allValue(es),
    (Stored)`(#%cons <Value v1> <Value v2>)` := lookup(pp, p.store);
    
CR red("5applyn", P p, (Expr)`(#%apply <Fun1 f> <Expr* es> #%null)`)
   = {<p, (Expr)`(<Fun1 f> <Expr* es>)`>}
   when
     allValue(es);


