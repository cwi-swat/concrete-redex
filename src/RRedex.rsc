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
 * - parameterize Ctx
 * - parameterize final configuration predicate
 * - make things generic on "conf"
 */

// result of rule function
alias CR = lrel[Tree,Tree];


// to be extended
default CR rule(str _, Tree _, Tree _) = [];


rel[tuple[Tree, Tree], str, tuple[Tree, Tree]] congruence(rel[Tree,Tree] matches, set[str] rules)
  = { <<ctx1, redex>, r, <ctx2, reduct>> |
      <Tree ctx1, Tree redex> <- matches, !(ctx1 is hole),
      str r <- rules,
      //bprintln("Trying <r> on <redex> in <ctx1>"),
      <Tree ctx2, Tree reduct> <- rule(r, ctx1, redex) };

//Trace[&T] traceGraph(Conf[&T] conf, set[str] rules) {
//  Trace[&T] trace = {};
//  set[Conf[&T]] confs = {conf};
//  while (confs != {}) {
//    set[Conf[&T]] newConfs = {};
//    for (Conf[&T] c1 <- confs) {
//      Trace[&T] steps = congruence(c1, rules);
//      trace += steps;
//      newConfs += steps<2>;
//    }
//    confs = newConfs;
//  }
//  return trace;
//}

// first in ctxs is the top context sort "correponding" to type of conf
void run(Tree conf, list[type[Tree]] ctxs, set[str] rules) {
  topCtx = ctxs[0];
  ctxSymbols = { c.symbol | type[Tree] c <- ctxs };
  
  int i = 0;
  bool stuck = false;
  while (!stuck) {
    println("ITER <i>");
    <prodMap, matches> = split(ctxSymbols, topCtx, conf);
    
    steps = congruence(matches, rules);
    println("#steps <size(steps)>");
    if (size(steps) == 0) {
      println("SPLITS:");
      for (<Tree c, Tree r> <- matches) {
        println("CTX: <c>   ");
        iprintln(c);
        println("RED: <r>    ");
      }
    }
    if (size(steps) > 1) {
      println("WARNING: non-determinism");
    }
    if (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
      println("Rule: <r>");
      println("Redex: <redex>");
      println("Reduct: <reduct>   blblbla");
      conf = plug(ctxSymbols, prodMap, ctx2, reduct);
      println("Newconf: <conf>   blablabla");
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
  Tree focused(Tree t) {
    t.prod.attributes += {\tag("category"("Focus"))};
    return t;
  }
  
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
  
// injection
bool match(Symbol s, appl(prod(_, [s], _), _)) = true;

default bool match(Symbol _, Tree _) = false; 

Symbol noLabel(label(_, Symbol s)) = s;
default Symbol noLabel(Symbol s) = s;  

tuple[map[Production, Production], rel[Tree, Tree]] split(set[Symbol] ctxSymbols, type[&T<:Tree] ctxType, Tree t) {
  //iprintln(ctxType.definitions);
  map[Production, Production] prodMap = ();
  
  void splitRec(Symbol ctxSort, Tree term, void(Tree, Tree) k) {
    set[Production] prods = ctxType.definitions[ctxSort].alternatives;
    
    nextProd: for (Production ctxProd <- prods) {
      //println("Trying prod: <ctxProd>");
      
      if (label("hole", _) := ctxProd.def) {
        //println("  fail because hole");
        continue nextProd;
      }
    
      // todo: deal with regulars
      if (size(term.prod.symbols) != size(ctxProd.symbols)) {
        //println("  fail because arity mismatch");
        continue nextProd;
      }

      int ctxPos = -1;
      Maybe[Symbol] maybeRec = nothing();
      for (int i <- [0..size(ctxProd.symbols)]) {
//        if (label("ctx", Symbol rec) := ctxProd.symbols[i]) {
        if (noLabel(ctxProd.symbols[i]) in ctxSymbols) {
          assert ctxPos == -1: "multiple holes in context";
          //println("  context arg: <noLabel(ctxProd.symbols[i])> at <i>");
          ctxPos = i;
          maybeRec = just(noLabel(ctxProd.symbols[i]));
        }
        else if (!match(noLabel(ctxProd.symbols[i]), term.args[i])) {
          //println("  fail because no match");
          continue nextProd;
        }
      }
      
      // comming here means prods are compatible modulo ctx recursive argument at ctxPos position
      assert ctxPos != -1;
      assert maybeRec != nothing();
      
      
      
      splitRec(maybeRec.val, term.args[ctxPos], (Tree subAlt, Tree redex) {
        // put original production inside the ctx production.
        //ctxProd.attributes = ctxProd.attributes + {\tag(term.prod)};
        //ctxProd@original = term.prod; // NB: these get lost when matching using concrete syntax to update context...
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
  //println("Result: <size(result)>");

  return <prodMap, result>;
}
