module paper::murebel::Ctx

import paper::murebel::Aux;

data C 
  = conf(Store store, Locks locks, S s, list[Stmt] stmts);


data SPar
  = block(list[Stmt] stmts1, S s, list[Stmt] stmts2)
  | inject(S s)
  ;


data S
  = hole(Stmt stmt)
  | block(S s, list[Stmt] stmts)
  | assign(E e, Id id, Expr expr)
  | assign(Value val, Id id, E e)
  | par(SPar spar)
  | syncLock(LIds lids, S s)
  | onSuccess(Ref ref, Id id, S s)
  | let(Id id, E e, Stmt stmt)
  | ifThen(E e, Stmt stmt)
  | ifThenElse(E e, Stmt stmt, Stmt stmt)
  | trigger(E e, Id id, list[Expr] exprs)
  | trigger(Value val, Id id, list[Value] vals, E e, list[Expr] exprs)
  ;
  
  
data E
  = hole(Expr expr)
  | field(E e, Id id)
  | not(E e)
  | mul(E e, Expr expr)
  | mul(Value, E e)
  | div(E e, Expr expr)
  | div(Value val, E e)
  | add(E e, Expr expr)
  | sub(Value val, E e)
  | gt(E e, Expr expr)
  | gt(Value val, E e)
  | geq(E e, Expr expr)
  | geq(Value val, E e)
  | leq(E e, Expr expr)
  | leq(Value val, E e)
  | lt(E e, Expr expr)
  | lt(Value val, E e)
  | eq(E e, Expr expr)
  | eq(Value val, E e)
  | neq(E e, Expr expr)
  | neq(Value val, E e)
  | and(E e, Expr expr)
  | or(E e, Expr expr)
  | \bracket(E e)
  ;
  