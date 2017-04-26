module Matching

import ParseTree;



alias B = map[str, Tree];
alias M = tuple[D, B];

data D
  = d(Ctx c, Tree t)
  | nil()
  ;
  

data Ctx
  = hole()
  | left(Ctx c, Tree t)
  | right(Tree t, Ctx c);

/*

variables
  C: C
  E: E
  t, t1, t2: Expr
  
context C
  = ☐: Expr
  | "if" C then Expr else Expr
  ;

generate:

syntax Ctx[C, Expr] = "C" "[" Expr "]" ... // when left act as pattern, when right it's plug
syntax Ctx[C, Expr] = @Var="true" "C"
syntax Rule
  = Pattern[Expr] "~>" Pattern[Expr]

syntax Pattern[Expr]
  = itself: Expr
  | Ctx[C, Expr]
  | "t"
  | "t1" ...
  
syntax Expr
  = Pattern[Expr]!itself
  ;  

*/


bool isHole(Tree t) = prod(_, [lit("☐")], _) := t.prod;
bool isVar(Tree t) = \tag("Var"(_)) <- t.prod.attributes;

default set[M] match(Grammar g, Tree p, Tree t) = {};

set[D] select(Tree t1,  nil(), Tree t2, nil()) = {nil()};
set[D] select(Tree t1,  d(c, t), Tree t2, nil()) = {d(left(c, t2),t)};
set[D] select(Tree t1,  nil(), Tree t2, d(c, t)) = {d(right(t1, c),t)};
set[D] select(Tree t1,  d(c1, t11), Tree t2, d(c2, t22)) = {};

Ctx concat(hole(), Ctx c) = c;
Ctx concat(left(c1, t), Ctx c2) = left(concat(c1, c2), t);
Ctx concat(right(t, c1), Ctx c2) = right(t, concat(c1, c2));

D combine(Ctx c, nil()) = nil();
D combine(Ctx c1, d(Ctx c2, Tree t)) = d(concat(c1, c2), t);  
  
Tree named(nil(), Tree t) = t;
Tree named(d(Ctx c, Tree t1), Tree t2) = C;
  
