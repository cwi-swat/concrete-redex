module paper::PTDiff

import ParseTree;
import util::Maybe;

alias Diff = Maybe[tuple[Tree,Tree]];

str diff2str(just(<t1, t2>)) = "\<<t1>, <t2>\>";
str diff2str(nothing()) = "nothing";

Diff ptDiff(Tree t1, Tree t2) {
  if (t1 == t2) {
    return nothing();
  }
  if (appl(Production p, list[Tree] args1) := t1,
      appl(p, list[Tree] args2) := t2) {
    for (int i <- [0..size(args1)]) { // todo: args don't need equal lengths with regulars.
      if (just(tuple[Tree,Tree] t) := ptDiff(args1[i], args2[i])) {
        return just(t);
      }
    }
    return nothing();    
  }
  return just(<t1, t2>);
}
