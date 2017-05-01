module RRedex

import ParseTree;
import List;
import IO;
import util::Maybe;
import String;

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
alias CR[&T] = list[&T];


// to be extended
default CR[void] rule(str _, Tree _) = [];


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

Tree plug(Tree ctx, Tree term) {
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

  return t;
}

// equals 
bool match(Symbol s, appl(prod(s, _, _), _)) = true;
  
// injection
bool match(Symbol s, appl(prod(_, [s], _), _)) = true;

default bool match(Symbol _, Tree _) = false; 

Symbol noLabel(label(_, Symbol s)) = s;
default Symbol noLabel(Symbol s) = s;  

Tree makeDummy(s:lit(str x)) = appl(prod(s, [/*???*/], {}), [ char(i) | int i <- chars(x) ]);
Tree makeDummy(s:layouts(_)) = appl(prod(s, [/* ??? */], {}), []);

// turn ctx,redex -> <ctx c>[<redex>]
Maybe[Tree] toSyntax(type[&T<:Tree] confType, Tree ctx, Tree redex) {
  set[Production] prods = confType.definitions[confType.symbol].alternatives;
  
  for (Production p <- prods, \tag("inContext"()) <- p.attributes) {
    list[Tree] newArgs = [];
    foundRedex = false;
    foundCtx = true;
    for (Symbol arg <- p.symbols) {
      if (label("ctx", Symbol s) := arg, s == ctx.prod.def) {
        newArgs += [ctx];
        foundCtx = true;
      } 
      else if (arg == redex.prod.def) {
        newArgs += [redex];
        foundRedex = true;
      }
      else {
        newArgs += [makeDummy(arg)];
      }
    }
    if (foundCtx && foundRedex) {
      return just(appl(p, newArgs));
    }
  }

  return nothing();
}

  
rel[Tree, Tree] split(set[Symbol] ctxSymbols, type[&T<:Tree] ctxType, Tree t) {
  //iprintln(ctxType.definitions);
  
  void splitRec(Symbol ctxSort, Tree term, void(Tree, Tree) k) {
    set[Production] prods = ctxType.definitions[ctxSort].alternatives;
    
    nextProd: for (Production ctxProd <- prods) {
      
      if (labeled("hole", _) := ctxProd.def) {
        continue nextProd;
      }
    
      // todo: deal with regulars
      if (size(term.prod.symbols) != size(ctxProd.symbols)) {
        continue nextProd;
      }

      int ctxPos = -1;
      Maybe[Symbol] maybeRec = nothing();
      for (int i <- [0..size(ctxProd.symbols)]) {
//        if (label("ctx", Symbol rec) := ctxProd.symbols[i]) {
        if (ctxProd.symbols[i] in ctxSymbols) {
          assert ctxPos == -1: "multiple holes in context";
          ctxPos = i;
          maybeRec = just(rec);
        }
        else if (!match(noLabel(ctxProd.symbols[i]), term.args[i])) {
          continue nextProd;
        }
      }
      
      // comming here means prods are compatible modulo ctx recursive argument at ctxPos position
      assert ctxPos != -1;
      assert maybeRec != nothing();
      
      
      splitRec(maybeRec.val, term.args[ctxPos], (Tree subAlt, Tree redex) {
        // put original production inside the ctx production.
        ctxProd = ctxProd[attributes=ctxProd.attributes + {\tag(term.prod)}];
        k(appl(ctxProd, term.args[0..ctxPos] + [subAlt] + term.args[ctxPos+1..]), redex);
      });
      
    }
    
    // coming here means, no prod could be used to split term
    // hence make empty context; and term becomes redex
    Tree empty = appl(prod(label("hole",ctxType.symbol),[lit("☐")],{}),[
             appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
    k(empty, term); // 
  }
  
  rel[Tree,Tree] result = {};
  splitRec(ctxType.symbol, t, (Tree ctx, Tree redex) {
    result += {<ctx, redex>};
  });
  return result;
  
}
