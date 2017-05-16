module paper::TraceRedex

import ParseTree;

alias R = set[Tree];
alias T = rel[Tree from, Tree to]; // traces

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

T trace(R(&T<:Tree) step, &T t0) {
  T trace = [];
  set[Tree] todo = {t0};
  solve (trace) {
    set[Tree] newTodo = {};
    for (&T t1 <- todo) {
      R next = step(t1);
      trace += [ <t1, t2> | t2 <- next ];
      newTodo += next;
    }
    todo = newTodo;
  }
  return trace;
}

