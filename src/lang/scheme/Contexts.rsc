module lang::scheme::Contexts

import lang::scheme::Scheme;

data E 
  = hole(loc redex)
  | apply(list[Expr] exprs1, E ctx, list[Expr] exprs2)
  | setBang(Id x, E ctx)
  | begin(E ctx, list[Expr] exprs)
  | ite(E ctx, Expr then, Expr els)
  ;
  
data P
  = conf(map[Id,Value] store, E ctx)
  ;
  
data Conf
  = conf(map[Id, Value] store, Expr term);
