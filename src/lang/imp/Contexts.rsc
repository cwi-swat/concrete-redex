module lang::imp::Contexts

import lang::imp::IMP;

data AE(Maybe[AExp] original = nothing())
  = add(AE ae, AExp aexp)
  | add(AExp aexp, AE ae)
  | div(AE ae, AExp aexp)
  | div(AExp aexp, AE ae)
  | hole(loc redex)
  ;
  
data BE(Maybe[BExp] original = nothing())
  = leq(AE ae, AExp aexp)
  | leq(Int n, AE ae)
  | not(BE be)
  | and(BE be, BExp bexp)
  | hole(loc redex)
  ;
  
data S(Maybe[Stmt] original = nothing())
  = assign(Id var, AE ae)
  | seq(S s, Stmt stmt)
  | ite(BE be, Stmt then, Stmt els)
  | hole(loc redex)
  ;
  
data C(Maybe[Conf] original = nothing())
  = conf(map[Id, Int] state, S s)
  ;
  
