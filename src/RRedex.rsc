module RRedex

import ParseTree;
import List;
import IO;
import util::Maybe;
import String;
import Set;


/*
 * - matching list patterns e.g.: Value, {Expr ","}*
 * - matching treeof Expr* should match Value* if injection between value->expr
 * - look over arbitrary levels of injections not just one.
 *
 * - trace graphs
 */

// result of rule function
alias CR = tuple[Tree context, Tree reduct];

// to be extended
default CR rule(str _, Tree _, Tree _) = dummy;

private tuple[Tree,Tree] dummy 
  = <appl(prod(sort("null"), [], {}), [char(110),char(117),char(108),char(108)]),
    appl(prod(sort("null"), [], {}), [char(110),char(117),char(108),char(108)])>;

alias Trace = rel[tuple[Tree,Tree] from, str rule, tuple[Tree, Tree] to];

Trace reductions(rel[Tree,Tree] matches, set[str] rules)
  = { <<ctx, redex>, r, <cr.context, cr.reduct>> |
      <Tree ctx, Tree redex> <- matches, !(ctx is hole),
      str r <- rules,
      //bprintln("Trygin rule <r>"),
      CR cr := rule(r, ctx, redex), cr != dummy
      };

rel[&T, str, Tree, &T] viewableTraceGraph(type[&T<:Tree] confType, type[&Ctx<:Tree] ctxType, &T conf, set[str] rules) {
  rel[&T, str, Tree, &T] trace = {};
  
  set[&T] confs = {conf};
  int i = 0;
  while (confs != {}) {
    set[&T] newConfs = {};
    for (&T c1 <- confs) {
      rel[Tree, Tree] matches = parseSplit(ctxType, c1);
      steps = reductions(matches, rules);
      for (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
        if (&T c2 := parsePlug(confType, ctx2, reduct)) {
          //if (c1 == c2) {
          //  println("Reduction is same as source!");
          //  println("conf1: <c1>");
          //  println("ctx1: <ctx1>");
          //  println("redex: <redex>");
          //  println("rule: <r>");
          //  println("ctx2: <ctx2>");
          //  println("reduct: <reduct>");
          //  println("conf2: <c2>");
          //  return {};
          //}
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

Trace traceGraph(type[&T<:Tree] confType, type[&Ctx<:Tree] ctxType, &T conf, set[str] rules) {
  Trace trace = {};
  
  set[Tree] confs = {conf};
  while (confs != {}) {
    set[Tree] newConfs = {};
    for (Tree c1 <- confs) {
      rel[&Ctx, Tree] matches = parseSplit(ctxType, conf);
      steps = reductions(matches, rules);
      trace += steps;
      for (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
        newConfs += {parsePlug(confType, ctx2, reduct)};
      }
    }
    confs = newConfs;
  }
  return trace;
}
 
// first in ctxs is the top context sort "correponding" to type of conf
void run(type[&T<:Tree] termType, type[&Ctx<:Tree] ctxType, &T conf, set[str] rules) {
  int i = 0;
  bool stuck = false;
  while (!stuck) {
    println("ITER <i>");
    rel[&Ctx, Tree] matches = parseSplit(ctxType, conf);
    for (<x, y> <- matches) {
      println(x.prod);
      println(y.prod);
      println("C: <x>\nR:<y>");
    } 
    steps = reductions(matches, rules);
    println(size(steps));
    if (size(steps) > 1) {
      println("WARNING: non-determinism");
    }
    
    if (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
      println("Rule: <r>");
      println("Redex: <redex>");
      println("Reduct: <reduct>  ");
      conf = parsePlug(termType, ctx2, reduct);
      println("Newconf: <conf>   ");
    }
    else {
      stuck = true;
    }
    i += 1;
  }  
}

&T parsePlug(type[&T<:Tree] termType, Tree ctx, Tree reduct) {
  Tree t = visit (ctx) {
    case Tree h => reduct
      when h is hole
  };
  return parse(termType, "<t>");
}

rel[Tree,Tree] parseSplit(type[&T<:Tree] ctxType, Tree t) {
  ctxParse = parse(ctxType, "<t>", allowAmbiguity=true);
  rel[Tree, Tree] result = {};
  flattenAmbs(ctxParse, (Tree ctx, Tree redex) {
    result += {<ctx, redex>};
  });
  return result;
}
 
void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (t is hole) {
    Tree hole = appl(prod(label("hole",t.prod.def),[lit("☐")],{}),[
             appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
    k(hole, t.args[0]); // skip over "hole" injection
  }
  else {
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
}

