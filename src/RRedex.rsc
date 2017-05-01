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
      // <Tree ctx2, Tree reduct> <- rule(r, ctx1, redex)
      CR cr := rule(r, ctx, redex), cr != dummy
      };

rel[&T, str, Tree, &T] viewableTraceGraph(type[&T<:Tree] confType, &T conf, list[type[Tree]] ctxs, set[str] rules) {
  rel[&T, str, Tree, &T] trace = {};
  topCtx = ctxs[0];
  ctxSymbols = { c.symbol | type[Tree] c <- ctxs };
  
  set[&T] confs = {conf};
  int i = 0;
  while (confs != {}) {
    set[&T] newConfs = {};
    for (&T c1 <- confs) {
      println("at <i> C1 = <c1>");
      <prodMap, matches> = split(ctxSymbols, topCtx, c1);
      steps = reductions(matches, rules);
      for (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
        if (&T c2 := plug(ctxSymbols, prodMap, ctx2, reduct)) {
          if (c1 == c2) {
            println("Reduction is same as source!");
            println("conf1: <c1>");
            println("ctx1: <ctx1>");
            println("redex: <redex>");
            println("rule: <r>");
            println("ctx2: <ctx2>");
            println("reduct: <reduct>");
            println("conf2: <c2>");
            return {};
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

Trace traceGraph(Tree conf, list[type[Tree]] ctxs, set[str] rules) {
  Trace trace = {};
  topCtx = ctxs[0];
  ctxSymbols = { c.symbol | type[Tree] c <- ctxs };
  
  set[Tree] confs = {conf};
  while (confs != {}) {
    set[Tree] newConfs = {};
    for (Tree c1 <- confs) {
      <prodMap, matches> = split(ctxSymbols, topCtx, conf);
      steps = reductions(matches, rules);
      trace += steps;
      for (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
        newConfs += {plug(ctxSymbols, prodMap, ctx2, reduct)};
      }
    }
    confs = newConfs;
  }
  return trace;
}

// first in ctxs is the top context sort "correponding" to type of conf
void run(Tree conf, list[type[Tree]] ctxs, set[str] rules) {
  topCtx = ctxs[0];
  ctxSymbols = { c.symbol | type[Tree] c <- ctxs };
  
  int i = 0;
  bool stuck = false;
  while (!stuck) {
    println("ITER <i>");
    <prodMap, matches> = split(ctxSymbols, topCtx, conf);
    steps = reductions(matches, rules);
    
    if (size(steps) > 1) {
      println("WARNING: non-determinism");
    }
    
    if (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
      println("Rule: <r>");
      println("Redex: <redex>");
      println("Reduct: <reduct>  ");
      conf = plug(ctxSymbols, prodMap, ctx2, reduct);
      println("Newconf: <conf>   ");
    }
    else {
      stuck = true;
    }
    i += 1;
  }  
}

list[Tree] injectIfNeeded(list[Symbol] syms, list[Tree] args) {
  return for (int i <- [0..size(syms)]) {
    if (noLabel(syms[i]) != args[i].prod.def) {
      append appl(prod(syms[i], [args[i].prod.def], {}), [args[i]]);
    }
    else {
      append args[i];
    }
  }
}


anno bool Tree@reduct;

Tree plug(set[Symbol] ctxSymbols, map[Production,Production] prodMap, Tree ctx, Tree term) {
  bool isCtx(Tree t) = t has prod && t.prod.def in ctxSymbols;

  Tree t = visit (ctx) {
    case Tree aCtx => appl(p, injectIfNeeded(p.symbols, aCtx.args))
      when isCtx(aCtx),  Production p := prodMap[aCtx.prod]
    case Tree h => term[@reduct=true] //focused(term)
      when h is hole
  };

  return t;
}

// equals 
bool match(Symbol s, appl(prod(s, _, _), _)) = true;
  
// 1-level injection
bool match(Symbol s, appl(prod(_, [s], _), _)) = true;

default bool match(Symbol _, Tree _) = false; 

Symbol noLabel(label(_, Symbol s)) = s;
default Symbol noLabel(Symbol s) = s;  

tuple[map[Production, Production], rel[Tree, Tree]] split(set[Symbol] ctxSymbols, type[&T<:Tree] ctxType, Tree t) {

  map[Production, Production] prodMap = ();
  
  void splitRec(Symbol ctxSort, Tree term, void(Tree, Tree) k) {
    set[Production] prods = ctxType.definitions[ctxSort].alternatives;
    
    nextProd: for (Production ctxProd <- prods) {
      
      if (label("hole", _) := ctxProd.def) {
        continue nextProd;
      }
    
      // todo: deal with regulars
      if (size(term.prod.symbols) != size(ctxProd.symbols)) {
        continue nextProd;
      }

      int ctxPos = -1;
      Maybe[Symbol] maybeRec = nothing();
      for (int i <- [0..size(ctxProd.symbols)]) {
        if (noLabel(ctxProd.symbols[i]) in ctxSymbols) {
          assert ctxPos == -1: "multiple holes in context";
          ctxPos = i;
          maybeRec = just(noLabel(ctxProd.symbols[i]));
        }
        else if (!match(noLabel(ctxProd.symbols[i]), term.args[i])) {
          continue nextProd;
        }
      }
      
      // comming here means prods are compatible modulo ctx recursive argument at ctxPos position
      assert ctxPos != -1;
      assert maybeRec != nothing();
      
      splitRec(maybeRec.val, term.args[ctxPos], (Tree subAlt, Tree redex) {
        prodMap[ctxProd] = term.prod; 
        k(appl(ctxProd, term.args[0..ctxPos] + [subAlt] + term.args[ctxPos+1..]), redex);
      });
      
    }
    
    // coming here means, no prod could be used to split term
    // hence make empty context; and term becomes redex
    Tree hole = appl(prod(label("hole",ctxSort),[lit("☐")],{}),[
             appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
    k(hole, term); // 
  }
  
  rel[Tree,Tree] result = {};
  splitRec(ctxType.symbol, t, (Tree ctx, Tree redex) {
    result += {<ctx, redex>};
  });

  return <prodMap, result>;
}
