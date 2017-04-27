module RRedex

import ParseTree;
import List;
import IO;

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

// to be extended
syntax Ctx
  = hole: "☐"
  ;

// configurations
private alias C = tuple[Ctx ctx, Tree tree];

// the result of a rule
alias CR = list[C];

alias Trace = lrel[C from, str rule, C to];

// to be extended
default CR rule(_, _, Tree t) = [];


lrel[&T, &T] step(type[&T<:Tree] typ, &T conf, set[str] rules)
  =  [ <conf, plug(typ, ctx2, reduct)> | <Ctx ctx1, Tree redex> <- split(conf)
     , str r <- rules, <Ctx ctx2, Tree reduct> <- rule(r, ctx1, redex) ];   

Trace step(Tree conf, set[str] rules)
  = [ <<ctx1, redex>, r, <ctx2, reduct>> | <Ctx ctx1, Tree redex> <- split(conf)
     , str r <- rules, <Ctx ctx2, Tree reduct> <- rule(r, ctx1, redex) ];   

alias Stepper = tuple[bool() hasNext,  Trace() next];

Stepper stepper(type[&T<:Tree] typ, &T conf, set[str] rules) {
  bool stuck = false;
  Trace steps = [];
  bool hasNext() {
    Trace steps = step(conf, rules);
    return steps != [];
  }
  
  Trace next() {
    conf = plug(typ);
    return steps;
  }

}

&T removeFocus(&T<:Tree t) {
  return visit (t) {
    case a:appl(prod(Symbol d, list[Symbol] ss, {*as, \tag("category"("Focus"))}), list[Tree] args) 
      => appl(prod(d, ss, {*as}), args) 
  }
}

rel[&T, str, Tree, &T] traceGraph(type[&T<:Tree] typ, &T conf, set[str] rules) {
  rel[&T, str, Tree, &T] trace = {};
  set[&T] confs = {conf};
  while (confs != {}) {
    set[&T] newConfs = {};
    for (&T c1 <- confs) {
      Trace steps = step(c1, rules);
      for (<<_, Tree redex>, str rule, <Ctx ctx2, Tree reduct>> <- steps) {
        if (&T c2 := plug(typ, ctx2, reduct)) {
          trace += <c1, rule, redex, c2>;
          newConfs += c2; //removeFocus(c2);
        }
        else throw "Error";
      }
    }
    confs = newConfs;
  }
  return trace;
}

// todo: make something that generates trace graphs
void run(type[&T<:Tree] typ, &T conf, set[str] rules) {
  
  int i = 0;
  bool stuck = false;
  while (!stuck) {
    println("ITER <i>");
    Trace steps = step(conf, rules);
    if (size(steps) > 1) {
      println("WARNING: non-determinism");
    }
    if (<<Ctx ctx1, Tree redex>, str r,  <Ctx ctx2, Tree reduct>> <- steps) {
      println("Rule: <r>");
      println("Redex: <redex>");
      println("Reduct: <reduct>");
      conf = plug(typ, ctx2, reduct);
      println("Newconf: <conf>");
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

&T plug(type[&T<:Tree] typ, Tree ctx, Tree term) {
  Tree focused(Tree t) {
    t.prod.attributes += {\tag("category"("Focus"))};
    return t;
  }

  Tree t = visit (ctx) {
    case Tree aCtx => appl(p, injectIfNeeded(p.symbols, aCtx.args))
      when Ctx _ := aCtx, \tag(Production p) <- aCtx.prod.attributes
    case Tree h => term[@reduct=true] //focused(term)
      when h is hole
  };

  if (&T typedT := t) {
    return typedT;
  }
  throw "Could not make typed tree for <t>";
}

// equals 
bool match(Symbol s, appl(prod(s, _, _), _)) = true;
  
// injection
bool match(Symbol s, appl(prod(_, [s], _), _)) = true;

default bool match(Symbol _, Tree _) = false; 

Symbol noLabel(label(_, Symbol s)) = s;
default Symbol noLabel(Symbol s) = s;  
  
rel[Tree, Tree] split(Tree t) {
  set[Production] prods = (#Ctx).definitions[sort("Ctx")].alternatives;
  
  void splitRec(Tree term, void(Tree, Tree) k) {
    nextProd: for (Production ctx <- prods) {
      if (ctx is hole) {
        continue nextProd;
      }
    
      if (size(term.prod.symbols) != size(ctx.symbols)) {
        continue nextProd;
      }

      int ctxPos = -1;
      for (int i <- [0..size(ctx.symbols)]) {
        if (ctx.symbols[i] == sort("Ctx")) {
          assert ctxPos == -1: "multiple holes in context";
          ctxPos = i;
        }
        else if (!match(noLabel(ctx.symbols[i]), term.args[i])) {
          continue nextProd;
        }
      }
      
      // comming here means prods are compatible modulo ctx recursive argument at ctxPos position
      assert ctxPos != -1;
      
      
      splitRec(term.args[ctxPos], (Tree subAlt, Tree redex) {
        // put original production inside the ctx production.
        ctxProd = ctx[attributes=ctx.attributes + {\tag(term.prod)}];
        k(appl(ctxProd, term.args[0..ctxPos] + [subAlt] + term.args[ctxPos+1..]), redex);
      });
      
    }
    
    // coming here means, no prod could be used to split term
    // hence make empty context; and term becomes redex
    Tree empty = appl(prod(label("hole",sort("Ctx")),[lit("☐")],{}),[
             appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
    k(empty, term); // 
  }
  
  rel[Tree,Tree] result = {};
  splitRec(t, (Tree ctx, Tree redex) {
    result += {<ctx, redex>};
  });
  return result;
  
}
