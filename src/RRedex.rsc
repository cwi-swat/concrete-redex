module RRedex

import ParseTree;
import List;
import IO;

// to be extended
syntax Ctx
  = hole: "☐"
  ;

private alias C = tuple[Ctx ctx, Tree tree];
alias CR = list[C];

// to be extended
default CR rule(_, _, Tree t) = [];


lrel[C,C] step(Tree conf, set[str] rules)
  = [ <<ctx1, redex>, <ctx2, reduct>> | <Ctx ctx1, Tree redex> <- split(conf)
     , str r <- rules, <Ctx ctx2, Tree reduct> <- rule(r, ctx1, redex) ];   

// todo: make something that generates trace graphs
void run(type[&T<:Tree] typ, &T conf, set[str] rules) {
  
  int i = 0;
  bool stuck = false;
  while (!stuck) {
    println("ITER <i>");
    lrel[C, C] steps = step(conf, rules);
    println("BRANCH: <size(steps)>");
    if (<<Ctx ctx1, Tree redex>, <Ctx ctx2, Tree reduct>> <- steps) {
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


&T plug(type[&T<:Tree] typ, Tree ctx, Tree term) {
  Tree t = visit (ctx) {
    case Tree aCtx => appl(p, injectIfNeeded(p.symbols, aCtx.args))
      when Ctx _ := aCtx, \tag(Production p) <- aCtx.prod.attributes
    case Tree h => term
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

      int rec = -1;
      for (int i <- [0..size(ctx.symbols)]) {
        if (ctx.symbols[i] == sort("Ctx")) {
          rec = i;
        }
        else if (!match(noLabel(ctx.symbols[i]), term.args[i])) {
          continue nextProd;
        }
      }
      
      // prods are compatible modulo ctx recursive argument at rec position
      assert rec != -1;
      
      
      splitRec(term.args[rec], (Tree subAlt, Tree redex) {
         ctxProd = ctx[attributes=ctx.attributes + {\tag(term.prod)}];
         k(appl(ctxProd, term.args[0..rec] + [subAlt] + term.args[rec+1..]), redex);
      });
      
    }
    // this means, no prod could be used to split term
    // hence take empty context (todo: make indep of Ctx name)
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
