module lang::credex::TraceRedex

import ParseTree;
import IO;
import util::Benchmark;
import Set;

@doc{Set of result of reducing a term}
alias R = set[Tree];

@doc{Set of results including the rule label that was used}
alias RR = rel[str rule, Tree to];

@doc{An reduction trace, linking source to target via rule label}
alias TR = rel[Tree from, str rule, Tree to]; 


alias Iter[&T<:Tree] = tuple[bool() hasNext, &T() next];

@doc{Create a reactive stepper given a function doing one step and a start term.
NB: this function choses one possible future in the case of non-determinism.}
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

@doc{Get the sequence of steps according to `step`}
list[&T] steps(R(&T<:Tree) step, &T t0) {
  Iter[&T] s = stepper(step, t0);
  list[&T] l = [t0];
  // return [t0] + [ s.next() | s.hasNext() ]
  while (s.hasNext()) l += [s.next()];
  return l;
}

@doc{Obtain a trace relation from a given apply function and initial term.
When debug is true, no result is returned, but intermediate data is printed.}
TR trace(RR(&T<:Tree) apply, &T t0, bool debug = false) {
  TR trace = {};
  
  void block() {
    set[Tree] todo = {t0};
    int i = 0;
    
    while (todo != {}) {
      if (debug) {
        println("\n#### Iteration: <i> (#todo = <size(todo)>)");
      }
      set[Tree] newTodo = {};
      for (&T t1 <- todo) {
        if (debug) {
          println("<t1>");
        }
        RR next = apply(t1);
        int j = 0;
        for (debug, <str r, t2> <- next) {
          println("=== <r><size(next) > 1 ? "[<j>]" : ""> ===\>");
          println(t2);
          j += 1;
        }
        trace += { <t1, r, t2> | <str r, t2> <- next };
        
        newTodo += next<1>;
      }
      todo = newTodo;
      i += 1;
    }
  }
  
  int time = realTime(block);
  if (debug) {
    println("Realtime (s): <(1.0 * time) / 1000>");
  }
  
  return debug ? {} : trace;
}


