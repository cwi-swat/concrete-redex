module RRedex

import ParseTree;
import List;
import IO;
import util::Maybe;
import String;
import Set;

// result of rule function
alias CR = tuple[Tree context, Tree reduct];

// to be extended
default CR rule(str _, Tree _, Tree _) = dummy;

private CR dummy 
  = <appl(prod(sort("null"), [], {}), [char(110),char(117),char(108),char(108)]),
    appl(prod(sort("null"), [], {}), [char(110),char(117),char(108),char(108)])>;

alias Trace = rel[tuple[Tree,Tree] from, str rule, tuple[Tree, Tree] to];

Trace reductions(rel[Tree,Tree] matches, set[str] rules)
  = { <<ctx, redex>, r, <cr.context, cr.reduct>> |
      <Tree ctx, Tree redex> <- matches, !(ctx is hole),
      str r <- rules, CR cr := rule(r, ctx, redex), cr != dummy };

private void noChangeInReductionError(Tree c1, Tree ctx1, Tree redex, str r, Tree ctx2, Tree reduct, Tree c2) {
  println("Reduction is same as source!");
  reportStep(c1, ctx1, redex, r, ctx2, reduct, c2);
}

void reportStep(Tree c1, Tree ctx1, Tree redex, str r, Tree ctx2, Tree reduct, Tree c2) {
  println("Reduction: <c1> ⟹ <c2> [<r>]   ");
  println("Redex: <redex> ");
  println("Reduct: <reduct> ");
}

rel[&T, str, Tree, &T] traceGraph(type[&T<:Tree] confType, type[&Ctx<:Tree] ctxType, &T conf, set[str] rules) {
  rel[&T, str, Tree, &T] trace = {};
  
  set[&T] confs = {conf};

  while (confs != {}) {
    set[&T] newConfs = {};
    for (&T c1 <- confs) {
      rel[Tree, Tree] matches = split(ctxType, c1);
      steps = reductions(matches, rules);
      for (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
        if (&T c2 := plug(confType, ctx2, reduct)) {
          if (c1 == c2) {
            noChangeInReductionError(c1, ctx1, redex, r, ctx2, reduct, c2);
            return trace;
          }
          
          trace += {<c1, r, redex, c2>};
          newConfs += {c2};
        }
      }
    }
    i += 1;
    confs = newConfs;
  }
  return trace;
}

 
void run(type[&T<:Tree] termType, type[&Ctx<:Tree] ctxType, &T conf, set[str] rules) {
  int i = 0;
  bool stuck = false;
  while (!stuck) {
    println("#<i>");
    rel[Tree, Tree] matches = split(ctxType, conf);
    
    Trace steps = reductions(matches, rules);
    
    if (size(steps) > 1) { // technically this should check on matches...
      println("WARNING: non-unique decomposition");
    }
    
    if (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
      newConf = plug(termType, ctx2, reduct);
      reportStep(conf, ctx1, redex, r, ctx2, reduct, newConf);
      conf = newConf;
    }
    else {
      stuck = true;
    }
    i += 1;
  }  
}

&T plug(type[&T<:Tree] termType, Tree ctx, Tree reduct) {
  int holeCount = 0;
  bool inc() { holeCount += 1; return true; }
  
  Tree t = visit (ctx) {
    case Tree h => reduct
      when h is hole, inc()
  };
  
  assert holeCount > 0: "no hole substituted in context";
  assert holeCount == 1: "multiple holes substituted in context";
  
  return parse(termType, "<t>");
}

rel[Tree,Tree] split(type[&T<:Tree] ctxType, Tree t) {
  ctxParse = parse(ctxType, "<t>", allowAmbiguity=true);
  
  rel[Tree, Tree] result = {};
  flattenAmbs(ctxParse, (Tree ctx, Tree redex) {
    result += {<ctx, redex>};
  });
  
  return result;
}

Tree makeHole(Symbol sym) 
  = appl(prod(label("hole", sym),[lit("☐")],{}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
 
void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (t is hole) {
    k(makeHole(t.prod.def), t.args[0]); // skip over "hole" injection
    return;
  }
  
  switch (t) {
    case appl(Production p, list[Tree] args): {
      for (int i <- [0..size(args)]) {
        flattenAmbs(args[i], (Tree ctx, Tree redex) {
          k(appl(p, args[0..i] + [ctx] + args[i+1..]), redex); 
        });
      }
    }
    
    case amb(set[Tree] alts): {
      for (Tree a <- alts) {
        flattenAmbs(a, (Tree ctx, Tree redex) {
          k(ctx, redex);
        });
      } 
    }
  }
  
}

