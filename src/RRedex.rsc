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
      <prodMap, matches> = split(ctxSymbols, topCtx, c1);
      steps = reductions(matches, rules);
      for (<<Tree ctx1, Tree redex>, str r,  <Tree ctx2, Tree reduct>> <- steps) {
        if (&T c2 := plug(ctxSymbols, prodMap, ctx2, reduct)) {
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

void match(Symbol sym, int pos, list[Tree] args) {
 /*
     | \iter(Symbol symbol) // <13>
     | \iter-star(Symbol symbol)  // <14>
     | \iter-seps(Symbol symbol, list[Symbol] separators)      // <15> 
     | \iter-star-seps(Symbol symbol, list[Symbol] separators) // <16>
     */
     
     

}

list[Tree] flattened(list[Tree] args)
  = ( [] | it + flatten(t) | Tree t <- args );
  
list[Tree] flatten(appl(regular(_), list[Tree] args)) = args;
default list[Tree] flatten(Tree t) = [t];


//void theMatch(Symbol sym, list[Tree] args, void(int, int, list[Tree], list[Tree]) k) {
//  switch (sym) {
//  
//  case \iter-star(Symbol elt): {
//    // zero elts
//    k(-1, 0, [], args); 
//    
//    int i = 0;
//    while (i < size(args)) {
//      if (match(elt, args[i])) {
//        i += 1;
//        k(-1, i, args[0..i], args[i..]);
//      }
//    } 
//  }
//  
//  case \iter-seps(Symbol elt, list[Symbol] seps): {
//    if (size(args) == 0) {
//      return;
//    }
//    
//    // single elt must be present
//    if (!match(elt, args[0])) {
//      return;
//    }
//
//    k(-1, 1, [args[0]], args[1..]);
//    
//    int i = 1;
//    listMatch: while (i < size(args) - (size(seps) + 1)) {
//      for (Symbol sep <- seps) {
//        if (!match(sep, args[i])) {
//          println("Did not match sep: <sep> \<-\> <args[i]>");
//          break listMatch;   
//        }
//        i += 1;
//      }
//      if (!match(elt, args[i])) {
//        break listMatch;
//      }
//      i += 1;
//      k(-1, i, args[0..i], args[i..]);
//    } 
//  }
//  
//  case \iter-star-seps(Symbol elt, list[Symbol] seps): {
//    // zero elts
//    k(-1, 0, [], args); 
//    
//    // no more elts
//    if (size(args) == 0) {
//      return;
//    }
//    
//    // single elt
//    if (!match(elt, args[0])) {
//      return;
//    }
//      
//    k(-1, 1, [args[0]], args[1..]);
//    
//    int i = 1;
//    listMatch: while (i < size(args) - (size(seps) + 1)) {
//      for (Symbol sep <- seps) {
//        if (!match(sep, args[i])) {
//          println("Did not match sep: <sep> \<-\> <args[i]>");
//          break listMatch;   
//        }
//        i += 1;
//      }
//      if (!match(elt, args[i])) {
//        break listMatch;
//      }
//      i += 1;
//      k(-1, i, args[0..i], args[i..]);
//    } 
//  }
//  
//  default: {
//    if (sym in ctxSymbols) {
//      splitRec(sym, args[0], (Tree subAlt, Tree redex) {
//        prodMap[ctxProd] = term.prod; 
//        k(-1, 1, [subAlt], args[1..]);
//      });
//    }
//    if (match(sym, args[0])) {
//      k(-1, 1, [args[0]], args[1..]);
//    }
//  
//  }
//  
// } 
//}



tuple[map[Production, Production], rel[Tree, Tree]] split(set[Symbol] ctxSymbols, type[&T<:Tree] ctxType, Tree t) {

  map[Production, Production] prodMap = ();
  
  void splitRec(Symbol ctxSort, Tree term, void(Tree, Tree) k) {
    set[Production] prods = ctxType.definitions[ctxSort].alternatives;
    
    println("Ctxsort: <ctxSort>");
    println("Term: <term>");
    
    nextProd: for (Production ctxProd <- prods) {
      println("##### Trying prod: <ctxProd>");
      
      if (label("hole", _) := ctxProd.def) {
        continue nextProd;
      }
    
      //// todo: deal with regulars
      //if (size(term.prod.symbols) != size(ctxProd.symbols)) {
      //  continue nextProd;
      //}

      int ctxPos = -1;
      Maybe[Symbol] maybeRec = nothing();
      list[Tree] ctxArgs = [];
      
      list[Tree] termArgs = flattened(term.args);
      
      i = 0;
      ci = 0;
      while (ci < size(ctxProd.symbols)) {
        println("Ctx Symbol: <ctxProd.symbols[ci]>");
        println("Subtree: <termArgs[i]>");
      
        if (noLabel(ctxProd.symbols[ci]) in ctxSymbols) {
          assert ctxPos == -1: "multiple holes in context";
          ctxPos = ci;
          maybeRec = just(noLabel(ctxProd.symbols[ci]));
          println("Found recursion: <ctxPos> type= <ctxProd.symbols[ci]>");
        }
      
        else { //if (!match(noLabel(ctxProd.symbols[i]), term.args[i])) 
          switch (noLabel(ctxProd.symbols[ci])) {
            case reg:\iter(Symbol elt): {
              Tree t = appl(regular(reg), []);
              if (!match(elt, termArgs[i])) {
                continue nextProd; // it's a plus list
              }
              while (match(elt, termArgs[i])) {
                t.args += [termArgs[i]];
                i += 1;
              }
              ctxArgs += [t];
            }
              
            case reg:\iter-star(Symbol elt):  {
              Tree t = appl(regular(reg), []);
              while (match(elt, termArgs[i])) {
                t.args += [termArgs[i]];
                i += 1;
              }
              ctxArgs += [t];
            
            }
            case reg:\iter-seps(Symbol elt, list[Symbol] seps): {
              Tree t = appl(regular(reg), []);
              if (!match(elt, termArgs[i])) {
                continue nextProd; // it's a plus list
              }
              t.args += [termArgs[i]];
              i += 1;
              
              // now begin matching separators and next elem
              // if both success, only then add to t.args 
              listMatch: while (true) {
                int j = i;
                if (j < size(term.args) - size(seps) + 1) {
                  // match seps
                  for (Symbol sep <- seps) {
                    if (!match(sep, termArgs[j])) {
                      break listMatch;   
                    }
                    j += 1;
                  }
                  if (!match(elt, termArgs[j])) {
                    break listMatch;
                  }
                  // we have matched separator + element
                  // add them to term.
                  for (Symbol sep <- seps) {
                    t.args += [termArgs[i]];
                    i += 1;
                  }
                  t.args += [termArgs[i]];
                  i += 1;
                }
                else {
                  break;
                }
              }
              ctxArgs += [t];
            
            }
            
            
            case reg:\iter-star-seps(Symbol elt, list[Symbol] seps): {
              println("Iter star seps: <reg>");
              Tree t = appl(regular(reg), []);
              
              if (match(elt, termArgs[i])) {
                println("Matched first elt");
                t.args += [termArgs[i]];
                i += 1;
              
                // now begin matching separators and next elem
                // if both success, only then add to t.args
                int j = i;
                   
                listMatch: while (true) {
                  println("Loop j = <j>");
                  // 0 1 2 3 4 5 6 7 8 9 10
                  // ( _ 3 _ 1 _ 2 _ 3 _ ) 
                  if (j < size(termArgs) - size(seps) + 1) {
                    // match seps
                    for (Symbol sep <- seps) {
                      if (!match(sep, termArgs[j])) {
                        println("Did not match sep: <sep> \<-\> <termArgs[j]>");
                        break listMatch;   
                      }
                      j += 1;
                    }
                    if (!match(elt, termArgs[j])) {
                      println("Did not match elt: <elt> \<-\> <termArgs[j]>");
                      break listMatch;
                    }
                    j += 1;
                    // we have matched separator + element
                    // add them to term t.
                    for (Symbol sep <- seps) {
                      t.args += [termArgs[i]];
                      i += 1;
                    }
                    t.args += [termArgs[i]];
                    i += 1;
                    j = i;
                  }
                  else {
                    break;
                  }
                }
              }
              
              ctxArgs += [t];
            }
             
            default: 
              if (!match(noLabel(ctxProd.symbols[ci]), termArgs[i])) {
                continue nextProd;
              }
              else {
                ctxArgs += [termArgs[i]];
                i += 1;
              }
          }
          
        }
        ci += 1;
        //i += 1;
      }
      
      // comming here means prods are compatible modulo ctx recursive argument at ctxPos position
      assert ctxPos != -1;
      assert maybeRec != nothing();
      
      splitRec(maybeRec.val, termArgs[ctxPos], (Tree subAlt, Tree redex) {
        prodMap[ctxProd] = term.prod; 
        // NB: we insert subAlt, not replace, since ctxArgs has does not have
        // a value for the recursive argument.
        k(appl(ctxProd, ctxArgs[0..ctxPos] + [subAlt] + ctxArgs[ctxPos..]), redex);
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

&T parsePlug(type[&T<:Tree] termType, Tree ctx, Tree reduct) {
  Tree t = visit (ctx) {
    case Tree h => reduct
      when h is hole
  };
  return parse(termType, "<t>");
}

rel[&T,Tree] parseSplit(type[&T<:Tree] ctxType, Tree t) {
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
    k(hole, t);
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

