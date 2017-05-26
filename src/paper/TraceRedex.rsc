module paper::TraceRedex

import ParseTree;

alias R = set[Tree];
alias RR = rel[str rule, Tree to];
alias TR = rel[Tree from, str rule, Tree to]; // traces 

alias Iter[&T<:Tree] = tuple[bool() hasNext, &T() next];

Iter[&T<:Tree] stepper(R(&T<:Tree) step, &T t0) {
  &T cur = t0;
  
  bool hasNext_() {
    if (&T t <- step(cur)) {
      cur = t;
      return true;
    }
    return false;
  }
  
  &T next_() = cur;

  return <hasNext_, next_>;
}


list[&T] steps(R(&T<:Tree) step, &T t0) {
  Iter[&T] s = stepper(step, t0);
  list[&T] l = [t0];
  while (s.hasNext()) l += [s.next()];
  return l;
}

TR trace(RR(&T<:Tree) step, &T t0) {
  TR trace = {};
  set[Tree] todo = {t0};
  solve (trace) {
    set[Tree] newTodo = {};
    for (&T t1 <- todo) {
      RR next = step(t1);
      trace += { <t1, r, t2> | <str r, t2> <- next };
      newTodo += next<1>;
    }
    todo = newTodo;
  }
  return trace;
}


