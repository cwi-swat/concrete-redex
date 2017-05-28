module paper::murebel::Semantics

import paper::murebel::Reachability; 
extend paper::murebel::Contexts2; 
extend paper::ParseRedex; 
//extend paper::murebel::Aux; 
import String;
import ParseTree;
import List;
import IO;
import Type;
import util::Maybe;

set[str] muRebel() = {"noOpSeq", "seqFail", "onFail", "onSuccess", "ifT", "ifF", "if",
  "assign", "let", "this", "trigger", "sync", "syncFail", "syncSuccess",
  "field", "new", "add", "sub", "mul", "div", "gt", "lt", "geq", "leq",
  "eq", "neq", "and", "or", "not", "emptySeq", "noOpPar", "parFail", "inState", "bracket"};

TR traceProg(Prog p) {
  RR myApply(Conf c) = apply(#C, #Conf, CR(str n, C ctx, Tree t) {
      return red(n, p.spec, ctx, t); 
    }, c, muRebel());
  Stmt* ss = p.stmts;
  return trace(myApply, (Conf)`, ⊢ <Stmt* ss>`);
}

TR filterMuRebel(TR tr) 
  = filterTrace(tr, {"emptySeq", "noOpPar", "parFail", "seqFail", "noOpSeq", "syncFail", "syncSuccess"});

TR filterTrace(TR tr, set[str] exclude) {
  // this is way slow...
  for (r <- exclude, {<Tree b, r, Tree c>, <Tree a, str r1, b>, <c, str r2, Tree d>, *rest} := tr) {
    println("Removing <b> === <r> ===\> c");
    tr = {<a, "<r1>+<r>+<r2>", d>, *rest};
  }
  return tr;
}

Prog txProg() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/tx.mrbl|).top;

Prog txProgSmall() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/tx-small.mrbl|).top;

Prog txProgExample() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/example.mrbl|).top;

Prog txProgSync() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/sync.mrbl|).top;

Prog timProg() = parse(#start[Prog], |project://concrete-redex/src/paper/murebel/tim.mrbl|).top;

default CR red(str _, Spec _, C _, Tree t) = {};

// TODO: 
// - add reason to fail so we can see why it failed
// - for things that don't access the context, we could memoize...
//   but then we have to do the congruence/plugCtx trick to eliminate C from the arguments.

CR red("noOpSeq", Spec spec, C c, (Stmt)`{; <Stmt* ss>}`)
  = {<c, (Stmt)`{<Stmt* ss>}`>};

CR red("emptySeq", Spec spec, C c, (Stmt)`{}`)
  = {<c, (Stmt)`;`>};

CR red("seqFail", Spec spec, C c, (Stmt)`{fail; <Stmt* s>}`)
  = {<c, (Stmt)`fail;`>};

//CR red("noOpParSeq", Spec spec, C c, (Stmt)`par {; <Stmt* ss1>}`)
//  = {<c, (Stmt)`par {<Stmt* ss1>}`>};
//  
//CR red("parFailSeq", Spec spec, C c, (Stmt)`par {fail; <Stmt* ss2>}`)
//  = {<c, (Stmt)`fail;`>};

CR red("noOpPar", Spec spec, C c, (Stmt)`par ;`)
  = {<c, (Stmt)`;`>};
  
CR red("parFail", Spec spec, C c, (Stmt)`par fail;`)
  = {<c, (Stmt)`fail;`>};

CR red("onFail", Spec spec, C c, (Stmt)`onSuccess (<Ref _> ↦ <Id _>) fail;`)
  = {<c, (Stmt)`fail;`>};
  
CR red("onSuccess", Spec spec, C c, (Stmt)`onSuccess (<Ref r> ↦ <Id x>) ;`)
  = {<c[store=s2], (Stmt)`;`>}
  when // on success is always below a sync from a transition, so we can modify it here.
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

CR red("assign", Spec spec, C c, rx:(Stmt)`<Ref r>.<Id x> = <Value v>;`)
  = {<c[store=s2], (Stmt)`;`>} 
  when 
    !isLocked(c, r, rx),
    Obj obj1 := lookup(c.store, r),
    Obj obj2 := setField(obj1, x, v),
    Store s2 := update(c.store, obj2);


CR red("let", Spec spec, C c, (Stmt)`let <Id x> = <Value v> in <Stmt s>`)
  = {<c, subst(( (Expr)`<Id x>`:  (Expr)`<Value v>`), s)>};

@doc{Attempt to make a transition. This requires that the receiver reference is not locked
for reading or writing by a lock not inherited from above.}
CR red("trigger", Spec spec, C c, it_:(Stmt)`<Ref r>.<Id x>(<{Expr ","}* es>);`)
  = {<c[locks=locks], (Stmt)`sync (<LId lock>, <{LId ","}* xs>) if (<Expr cond>) onSuccess(<Ref r> ↦ <Id trg>) <Stmt body> else fail;`>}
  when allValue(es),
    {LId ","}* xs := enclosingLocks(c, it_),
    !isLocked(c, r, it_), // otherwise, we can't acquire the lock
    Obj obj := lookup(c.store, r),
    St cur := obj.state,
    Entity e := lookupEntity(spec, obj.class),
    State st := lookupState(e, cur),
    hasTransition(st, x),
    Trans t := normalize(lookupTransition(st, x), cur),
    {Formal ","}* fs := t.formals,
    arity(fs) == arity(es),
    Id trg := getTarget(t),
    map[Expr, Expr] sub := makeSubst(fs, es) + ((Expr)`this`: (Expr)`<Ref r>`),
    Expr cond := subst(sub, getPre(t)),
    Stmt body := subst(sub, t.body),
    LId lock := newLock(c.locks),
    Locks locks := addLock(c.locks, (Lock)`<LId lock> {<Obj obj> | <Obj obj>}`);

CR red("sync", Spec spec, C c, rx:(Stmt)`sync <Stmt s>`)
  = {<c[locks=locks2], (Stmt)`sync (<LId lock>, <{LId ","}* xs>) <Stmt s>`>}
  when 
    LId lock := newLock(c.locks),
    <set[Ref] reads, set[Ref] writes> := reachable(s, c.store, spec),
    
    {LId ","}* xs := enclosingLocks(c, rx),
    //set[Ref] allReads := reads + { obj.ref | Id x <- xs, Lock l := getLock(c.locks, x), Obj obj <- l.reads },
    //set[Ref] allWrites := writes + { obj.ref | Id x <- xs, Lock l := getLock(c.locks, x), Obj obj <- l.writes },
    
    // do we need to check this on allReads/Writes? The inherited refs are already protected.
    // and fail propagates always upwards 
    ( true | it && !isWriteLocked(c, r, rx) | Ref r <- reads ),
    ( true | it && !isLocked(c, r, rx) | Ref r <- writes ),

    list[Obj] readObjs := [ obj | Obj obj <- c.store.objs, obj.ref in reads ],
    list[Obj] writeObjs := [ obj | Obj obj <- c.store.objs, obj.ref in writes ],
    
    Lock theLock := makeLock(lock, readObjs, writeObjs),
    Locks locks2 := addLock(c.locks, theLock);
    

@doc{When fail ends up in a sync, we have to restore any objects referenced in the write locks
(read locks have only been read in this "thread" of execution so don't need restoring).} 
CR red("syncFail", Spec spec, C c, (Stmt)`sync (<LId x>, <{LId ","}* _>) fail;`)
  = {<c[locks=locks2][store=s2], (Stmt)`fail;`>} // restore old state from lockstore
  when
    Lock lock := getLock(c.locks, x), 
    Locks locks2 := deleteLock(c.locks, x),
    Store s2 := ( c.store | update(it, obj) | obj <- lock.writes );
    
@doc{Success simply means that the we can discard the lock and continue. The store
actually represents the desired state.}    
CR red("syncSuccess", Spec spec, C c, (Stmt)`sync (<LId x>, <{LId ","}* _>) ;`)
  = {<c[locks=locks], (Stmt)`;`>}
  when
    Locks locks := deleteLock(c.locks, x);


/*
 * Context helpers
 */

{LId ","}* enclosingLocks(C ctx, Tree redex) {
  if (just((S)`sync (<{LId ","}* xs>) <S _>`) := innerMostSync(ctx.stmt, nothing())) {
    return xs;
  }
  // Yikes...
  return typeCast(#{LId ","}*, appl(regular(\iter-star-seps(sort("LId"), 
    [layouts("Standard"), lit(","), layouts("Standard")])), []));
}

bool isReadLocked(C c, Ref r, Tree rx) = isReadLockedExcept(c.locks, r, { x | LId x <- xs })
   when {LId ","}* xs := enclosingLocks(c, rx);

bool isWriteLocked(C c, Ref r, Tree rx) = isWriteLockedExcept(c.locks, r, { x | LId x <- xs })
   when {LId ","}* xs := enclosingLocks(c, rx);

// avoid twice calling of enclosingLocks
bool isLocked(C c, Ref r, Tree rx) = isWriteLockedExcept(c.locks, r, except) || isReadLockedExcept(c.locks, r, except)
  when 
    {LId ","}* xs := enclosingLocks(c, rx),
    set[LId] except := { x | LId x <- xs };
  
  
/*
 * Expressions
 */

CR red("inState", Spec spec, C c, rx:(Expr)`<Ref r> in <Id x>`)
 = {<c, (St)`<Id x>` := lookup(c.store, r).state ? (Expr)`true` : (Expr)`false`>}
 when !isWriteLocked(c, r, rx); 
 

CR red("field", Spec spec, C c, rx:(Expr)`<Ref r>.<Id x>`)
  = {<c, (Expr)`<Value v>`>}
  when  // TODO: check initialized
    !isWriteLocked(c, r, rx),
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
  
CR red("bracket", Spec spec, C c, (Expr)`(<Value v>)`) 
  = {<c, (Expr)`<Value v>`>};   
  