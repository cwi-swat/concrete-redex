module paper::murebel::Semantics

extend paper::murebel::Contexts; 
extend paper::ParseRedex;
import paper::Substitution;
import String;
import ParseTree;
import List;
import IO;

set[str] muRebel() = {"noOpSeq", "eagerFailSeq", "onFail", "onSuccess", "ifT", "ifF", "if",
  "assign", "let", "this", "trigger", "sync", "syncFail", "syncSuccess",
  "field", "new", "add", "sub", "mul", "div", "gt", "lt", "geq", "leq",
  "eq", "neq", "and", "or", "not", "emptySeq", "noOpPar"};

TR traceProg(Prog p) {
  RR myApply(Conf c) = apply(#C, #Conf, CR(str n, C c, Tree t) {
      return red(n, p.spec, c, t); 
    }, c, muRebel());
  Stmt* ss = p.stmts;
  return trace(myApply, (Conf)`, ⊢ <Stmt* ss>`);
}


//RR applyMuRebel(Co p) 
//  = apply(#C, #Conf, CR(str n, C c, Tree t) {
//      return red(n, p.spec, c, t); 
//    }, (Conf)`, ⊢ <Stmt* ss>`, muRebel())
//    when Stmt* ss := p.stmts;
    
//R reduceMuRebel(Prog p, Conf c) = reduce(#C, #Conf, red, c, muRebel());

Prog txProg() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/tx.mrbl|).top;

Prog txProgSmall() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/tx-small.mrbl|).top;

default CR red(str _, Spec _, C _, Tree _) = {};

//CR red("nestedSeq", Spec spec, C c, (Stmt)`{{<Stmt* s>}}`)
//  = {<c, (Stmt)`{<Stmt* s> <Stmt* s2>}`>};

CR red("noOpSeq", Spec spec, C c, (Stmt)`{; <Stmt* s>}`)
  = {<c, (Stmt)`{<Stmt* s>}`>};
//
CR red("emptySeq", Spec spec, C c, (Stmt)`{}`)
  = {<c, (Stmt)`;`>};

// design choice? 
CR red("eagerFailSeq", Spec spec, C c, (Stmt)`{fail; <Stmt* s>}`)
  = {<c, (Stmt)`fail;`>};

CR red("noOpPar", Spec spec, C c, (Stmt)`par ;`)
  = {<c, (Stmt)`;`>};
  

CR red("onFail", Spec spec, C c, (Stmt)`onSuccess (<Ref _> ↦ <Id _>) fail;`)
  = {<c, (Stmt)`fail;`>};
  
CR red("onSuccess", Spec spec, C c, (Stmt)`onSuccess (<Ref r> ↦ <Id x>) ;`)
  = {<c[store=s2], (Stmt)`;`>}
  when 
    Obj obj1 := lookup(c.store, r),
    Obj obj2 := gotoState(obj1, x),
    Store s2 := update(c.store, obj2);

CR red("ifT", Spec spec, C c, (Stmt)`if (true) <Stmt s1> else <Stmt s2>`)
  = {<c, s1>};  

CR red("ifF", Spec spec, C c, (Stmt)`if (<Value v>) <Stmt s1> else <Stmt s2>`)
  = {<c, s2>}
  when (Value)`true` !:= v;
  
CR red("if", Spec spec, C c, (Stmt)`if (<Value v>) <Stmt s>`)
  = {<c, (Stmt)`if (<Value v>) <Stmt s> else ;`>};

CR red("assign", Spec spec, C c, (Stmt)`<Ref r>.<Id x> = <Value v>;`)
  = {<c[store=s2], (Stmt)`;`>} 
  when 
    Obj obj1 := lookup(c.store, r),
    Obj obj2 := setField(obj1, x, v),
    Store s2 := update(c.store, obj2);


CR red("let", Spec spec, C c, (Stmt)`let <Id x> = <Value v> in <Stmt s>`)
  = {<c, subst(( (Expr)`<Id x>`:  (Expr)`<Value v>`), s)>};

/*
 * look up x in current state of r
 * if exists, is initialized, with target t, body b, and pre p, rewrite to 
 *  sync(lockForROnly) if (p) onSuccess(r ↦ t) b else fail;
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
CR red("trigger", Spec spec, C c, it_:(Stmt)`<Ref r>.<Id x>(<{Expr ","}* es>);`)
  = {<c[locks=locks], (Stmt)`sync (<Id lock>) if (<Expr cond>) onSuccess(<Ref r> ↦ <Id trg>) <Stmt body> else fail;`>}
  when allValue(es), !isLocked(c.locks, r),
    bprintln("======\> <it_>  "),
    bprintln("<c.store> "),
    Obj obj := lookup(c.store, r),
    St cur := obj.state,
    bprintln("Current state: <cur>"),
    bprintln("obj = <obj>"),
    Entity e := lookupEntity(spec, obj.class),
    State st := lookupState(e, cur),
    hasTransition(st, x),
    bprintln("FOUND trans!"),
    Trans t := normalize(lookupTransition(st, x), cur),
    bprintln("FOUND trans: <t>"),
    {Formal ","}* fs := t.formals,
    bprintln("formals <fs>"),
    bprintln("arity formals: <arity(fs)>"),
    bprintln("arity args: <arity(es)>"),
    arity(fs) == arity(es),
    bprintln("arity = ok (t = <t>)"),
    Id trg := getTarget(t),
    bprintln("target state <trg>"),
    map[Expr, Expr] sub := makeSubst(fs, es) + ((Expr)`this`: (Expr)`<Ref r>`),
    bprintSub(sub),
    Expr cond := subst(sub, getPre(t)),
    bprintln("Pre condition: <cond>"),
    Stmt body := subst(sub, t.body),
    bprintln("Body <body>"),
    Id lock := newLock(c.locks),
    bprintln("Lock = <lock>"),
    bprintln("c.locks = <c.locks>"),
    Obj obj := lookup(c.store, r),
    Locks locks := addLock(c.locks, (Lock)`<Id lock> {<Obj obj>}`);

//    /(ES)`sync (<Id lock>) {<S s>}` := e; 

CR red("sync", Spec spec, C c, (Stmt)`sync <Stmt s>`)
  = {<c[locks=locks2], (Stmt)`sync (<Id lock>) <Stmt s>`>}
  when 
    Id lock := newLock(c.locks),
    Obj* objs := c.store.objs, // lock the whole store: TODO: should be fields of "this", how?
    // for all refs in "active" position lock the object?
    // so as receiver of assignment or in call.
    //  r.t() -> lock r
    //  r.f.t() -> lock r and r.f
    //  r.f = x -> lock r and r.f
    // and objects the fields actually refer to?
    // but also transitively if transitions fire other transitions as well.
    // we need *all* participants.   
    // maybe: copy whole store to lock
    // if in assignment to ref r under lock, mark the locked object as dirty
    // same if any transition on ref r is performed
    // then only restore dirty bits; NO: this only makes
    // restore a bit cheaper, but it doesn't allow lock checking
    Locks locks2 := addLock(c.locks, (Lock)`<Id lock> { <Obj* objs> }`);
    
  
CR red("syncFail", Spec spec, C c, (Stmt)`sync (<Id x>) fail;`)
  = {<c[locks=locks2][store=s2], (Stmt)`fail;`>} // restore old state from lockstore
  when
    Lock lock := getLock(c.locks, x), 
    Locks locks2 := deleteLock(c.locks, x),
    Store s2 := ( c.store | update(it, obj) | obj <- lock.objs );
    
    
CR red("syncSuccess", Spec spec, C c, (Stmt)`sync (<Id x>) ;`)
  = {<c[locks=locks], (Stmt)`;`>}
  when
    Locks locks := deleteLock(c.locks, x);
  
  
/*
 * Expressions
 */

CR red("field", Spec spec, C c, (Expr)`<Ref r>.<Id x>`)
  = {<c, (Expr)`<Value v>`>}
  when 
    Obj obj := lookup(c.store, r),
    Value v := getField(obj, x);
    

CR red("new", Spec spec, C c, (Expr)`new <Id x>`)
  = {<c[store=s2], (Expr)`#<Num ptr>`>}
  when 
    list[int] ns := [ toInt(obj.ref.ptr) | Obj obj <- c.store.objs ],
    int n := ((ns == []) ? 0 : 1 + max(ns)),
    Num ptr := [Num]"<n>",
    Store s2 := addObj(c.store, (Obj)`#<Num ptr> : <Id x> [⊥] { }`);

CR red("add", Spec spec, C c, (Expr)`<Num i1> + <Num i2>`) 
  = {<c, intExpr(toInt(i1) + toInt(i2))>}; 

CR red("sub", Spec spec, C c, (Expr)`<Num i1> - <Num i2>`) 
  = {<c, intExpr(toInt(i1) - toInt(i2))>}; 

CR red("mul", Spec spec, C c, (Expr)`<Num i1> * <Num i2>`) 
  = {<c, intExpr(toInt(i1) * toInt(i2))>}; 

CR red("div", Spec spec, C c, (Expr)`<Num i1> / <Num i2>`) 
  = {<c, intExpr(toInt(i1) / toInt(i2))>}; 

CR red("gt", Spec spec, C c, (Expr)`<Num i1> \> <Num i2>`) 
  = {<c, boolExpr(toInt(i1) > toInt(i2))>}; 

CR red("lt", Spec spec, C c, (Expr)`<Num i1> \< <Num i2>`) 
  = {<c, boolExpr(toInt(i1) < toInt(i2))>}; 

CR red("geq", Spec spec, C c, (Expr)`<Num i1> \>= <Num i2>`) 
  = {<c, boolExpr(toInt(i1) >= toInt(i2))>}; 

CR red("leq", Spec spec, C c, (Expr)`<Num i1> \<= <Num i2>`) 
  = {<c, boolExpr(toInt(i1) <= toInt(i2))>}; 

CR red("eq", Spec spec, C c, (Expr)`<Value v1> == <Value v2>`) 
  = {<c, boolExpr(v1 == v2)>}; 

CR red("neq", Spec spec, C c, (Expr)`<Value v1> != <Value v2>`) 
  = {<c, boolExpr(v1 != v2)>}; 

CR red("and", Spec spec, C c, (Expr)`<Bool b> && <Expr e>`) 
  = {<c, (Bool)`true` ? e : boolExpr(false)>}; 

CR red("or", Spec spec, C c, (Expr)`<Bool b> || <Expr e>`) 
  = {<c, (Bool)`false` ? e : boolExpr(true)>}; 

CR red("not", Spec spec, C c, (Expr)`!<Bool b>`) 
  = {<c, boolExpr(b != (Bool)`true`)>};   
  
