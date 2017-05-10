module lang::lambda::Contexts

import lang::lambda::Lambda;
import credex::Matching;
import ParseTree;
import Type;
import List;
import IO;
import Node;

data E
  = apply(list[Value] vals, E ctx, list[Expr] exprs)
  | if0(E ctx, Expr then, Expr els)
  | hole()
  ;
  
