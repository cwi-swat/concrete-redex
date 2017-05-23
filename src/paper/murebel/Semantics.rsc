module paper::murebel::Semantics

import paper::murebel::Contexts;
extend paper::ParseRedex;
import String;

CR red("onFail", P p, (Stmt)`onSuccess (<Ref _> ↦ <Id _>) fail;`)
  = {<p, (Stmt)`fail;`>};
  
CR red("onSuccess", P p, (Stmt)`onSuccess (<Ref r> ↦ <Id x>) ;`)
  = {<p, (Stmt)`;`>}; // and update store to reflect new state for r

CR red("ifT", P p, (Stmt)`if (true) <Stmt s1> else <Stmt s2>`)
  = {<p, s1>};  

CR red("ifF", P p, (Stmt)`if (<Value v>) <Stmt s1> else <Stmt s2>`)
  = {<p, s2>}
  when (Value)`true` !:= v;
  
CR red("if", P p, (Stmt)`if (<Value v>) <Stmt s>`)
  = {<p, (Stmt)`if (<Value v>) <Stmt s> else ;`>};

CR red("assign", P p, (Stmt)`<Ref r>.<Id x> = <Value v>`)
  = {<p, (Stmt)`;`>}; // and update store


CR red("let", P p, (Stmt)`let <Id x> = <Value v> in <Stmt s>`)
  = {<p, subst((Expr)`<Id x>`, (Expr)`<Value v>`, s)>};

/*
 * look up x in current state of r
 * if exists, is initialized, with target t, body b, and pre p, rewrite to if (p) r ↦ t b else fail;
 * (and substitute formals for actuals in both b and p, as well as "this" for r)
 * else fail
 * also fail when r is locked
 * here we need nested context matching to find the innermost enclosing sync(lock) construct
 * and add the obj of r to the lock store
 * -> again choice: if there are multiple triggers on the same r, do they see each others updates?
 *   if not, we need to read from the lock store, or fail.
 * -> choice: lock all participants at sync, or at trigger?
 * so two cases triggerSync and trigger
 */
CR red("trigger", P p, (Stmt)`<Ref r>.<Id x>(<{Expr ","}* es>);`)
  = {<p, x>}
  when allValue(es); 
  
CR red("sync", P p, (Stmt)`sync <Stmt s>`)
  = {<p, (Stmt)`sync (<Id lock>) <Stmt s>`>}
  when 
    Id lock := fresh("l", { l.id | Lock l <- p.locks });
  
CR red("syncFail", P p, (Stmt)`sync (<Id lock>) fail;`)
  = {<p, x>}; // restore old state from lockstore

CR red("syncSuccess", P p, (Stmt)`sync (<Id lock>) ;`)
  = {<p, x>}; // remove the lock from locks
  
  
/*
 * Expressions
 */

CR red("field", P p, (Expr)`<Ref r>.<Id x>`)
  = todo;

CR red("new", P p, (Expr)`new <Id x>`)
  = todo;

CR red("add", P p, (Expr)`<Num i1> + <Num i2>`) 
  = {<p, intExpr(toNum(i1) + toNum(i2))>}; 

CR red("sub", P p, (Expr)`<Num i1> - <Num i2>`) 
  = {<p, intExpr(toNum(i1) - toNum(i2))>}; 

CR red("mul", P p, (Expr)`<Num i1> * <Num i2>`) 
  = {<p, intExpr(toNum(i1) * toNum(i2))>}; 

CR red("div", P p, (Expr)`<Num i1> / <Num i2>`) 
  = {<p, intExpr(toNum(i1) / toNum(i2))>}; 

CR red("gt", P p, (Expr)`<Num i1> \> <Num i2>`) 
  = {<p, boolExpr(toNum(i1) > toNum(i2))>}; 

CR red("lt", P p, (Expr)`<Num i1> \< <Num i2>`) 
  = {<p, boolExpr(toNum(i1) < toNum(i2))>}; 

CR red("geq", P p, (Expr)`<Num i1> \>= <Num i2>`) 
  = {<p, boolExpr(toNum(i1) >= toNum(i2))>}; 

CR red("leq", P p, (Expr)`<Num i1> \<= <Num i2>`) 
  = {<p, boolExpr(toNum(i1) <= toNum(i2))>}; 

CR red("eq", P p, (Expr)`<Value v1> == <Value v2>`) 
  = {<p, boolExpr(v1 == v2)>}; 

CR red("neq", P p, (Expr)`<Value v1> != <Value v2>`) 
  = {<p, boolExpr(v1 != v2)>}; 

CR red("and", P p, (Expr)`<Bool b> && <Expr e>`) 
  = {<p, (Bool)`true` ? e : boolExpr(false)>}; 

CR red("or", P p, (Expr)`<Bool b> || <Expr e>`) 
  = {<p, (Bool)`false` ? e : boolExpr(true)>}; 

CR red("not", P p, (Expr)`!<Bool b>`) 
  = {<p, boolExpr(b != (Bool)`true`)>};   
  
/*
 * Helper functions
 */

int toNum(Num i) = toInt("<i>");

Expr intExpr(int n) = (Expr)`<Num i>` when Num i := [Num]"<n>";

Expr boolExpr(bool b) = b ? (Expr)`true` : (Expr)`false`;