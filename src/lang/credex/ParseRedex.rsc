module lang::credex::ParseRedex

import ParseTree;
import List;
import Set;
import Type;
import IO;

extend lang::credex::TraceRedex;


/*
 * Applying reduction relations
 */

alias CR = rel[Tree context, Tree reduct]; // context reduct pairs

RR apply(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules)
  = { <r, typeCast(#Tree, plug(tt, ctx2, rt))> |
    //bprintln("\nSTARTING REDUCTION"),  
     <&C ctx1, Tree rx> <- split(ct, t),
    //bprintln("ctx = <ctx1>"),
    //bprintln("redex = <rx>"),
     str r <- rules,
     //bprintln("RULE: <r>"),
     <&C ctx2, Tree rt> <- red(r, ctx1, rx)
     //, bprintln("<rx> === <r> ===\> <rt>")
      };


void printDecompositions(type[&C<:Tree] ct, Tree t) {
  for (<&C ctx, Tree rx> <- split(ct, t)) {
    println("CTX: <ctx> ");
    println("REDEX: <rx> ");
  }
}

RR apply2(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules) {
  ctx = myParse(ct, "<t>", t@\loc, allowAmbiguity=true);
  RR rr = {};
  flattenAmbs(ctx, (Tree alt, Tree rx) {
    rr +=  { <r, plug(tt, ctx2, rt)> | 
      str r <- rules, &C ctx1 := alt, 
      <&C ctx2, Tree rt> <- red(r, ctx1, rx), bprintln("<rx> === <r> ===\> <rt>") };
  });
  return rr;
}


&T myParse(type[&T<:Tree] t, str src, loc l, bool allowAmbiguity = false) {
  //println("PARSING as <t>: `<src>`");
  return parse(t, src, l, allowAmbiguity=allowAmbiguity);
}

&T myParse(type[&T<:Tree] t, str src bool allowAmbiguity = false) {
  //println("PARSING as <t>: `<src>`");
  return parse(t, src, allowAmbiguity=allowAmbiguity);
}

R reduce(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules)
  = apply(ct, tt, red, t, rules)<1>;

/*
 * Checking context grammars:
 * ensure that every context has exactly one hole
 */
 
bool checkContext(type[&C<:Tree] ct) = true; // todo


/*
 * Split and plug
 */

Tree plugCtx(type[&C<:Tree] ct, Tree ctx1, &C ctx2) {
  result = top-down-break visit (ctx1) {
    case &C t => ctx2 when t@\loc == ctx1@\loc
  }
  return result;
}

@doc{Check if redex is in a context's hole}
bool inHole(Tree t, Tree redex) = true
  when t is hole && t.args[0] == redex; //t@\loc == redex@\loc;
  
bool inHole(t:appl(Production p, list[Tree] args), Tree redex) 
  = inHole(arg, redex)
  when 
    Tree arg <- args,  arg@\loc?, redex@\loc <= arg@\loc;
  

@doc{Split a term according to the provided context grammar}
rel[Tree,Tree] split(type[&T<:Tree] ctxType, Tree t) {
  try {
    ctx = myParse(ctxType, "<t>", t@\loc, allowAmbiguity=true);
  
    rel[int, Tree, Tree] result = {};
    int maxDepth = -1;
    flattenAmbs(ctx, 0, (int depth, Tree alt, Tree redex) {
      // could we do the reductions here, without flattening it all?
      // (a kind of deforestation)
      //println("DEPTH: <depth>");
      if (depth >= maxDepth) {
        maxDepth = depth;
      }
      result += {<depth, alt, redex>};
    });
    
    return { <c, trm> | <_, Tree c, Tree trm> <- result };
    
  }
  catch ParseError(loc _): {
    // stuck
    return {};
  }
}

str getSort(label(_, sort(str name))) = name; 
str getSort(sort(str name)) = name; 
default str getSort(Symbol _) = "";

bool isContext(Tree t) = /^[A-Z]$/ := getSort(t.prod.def) || t is hole;

// log(n) plug function (not using visit).
Tree plug2(Tree ctx, Tree reduct) {
  assert isContext(ctx) : "plug not traversing context <ctx>";

  if (ctx is hole) {
    return reduct;
  }
  // for now, use capital single letter as convention
  if (appl(Production p, list[Tree] args) := ctx, int i <- [0..size(args)]
      //, bprintln("looking for context at <i>: <args[i]> (sym = <args[i].prod.def>)")
      , isContext(args[i])) {
    //println("Found it at <i>: <args[i]>");
    return appl(p, args[0..i] + [plug2(args[i], reduct)] + args[i+1..])[@\loc=ctx@\loc];
  }
  
  assert false:  "no hole found: <ctx>";
}

@doc{Plug reduct back into context, turning it into a term}
&T plug(type[&T<:Tree] tt, Tree ctx, Tree reduct) {
  //Tree t = bottom-up-break visit (ctx) {
  //  case Tree h => reduct when h is hole
  //};
  Tree t = plug2(ctx, reduct);
  return myParse(tt, "<t>");
}

private Tree makeHole(Symbol sym, loc l) 
  = appl(prod(label("hole", sym),[lit("☐")],{}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])])[@\loc=l];
 
bool allSameProd(set[Tree] ts) {
  if (ts == {}) return true;
  p = getOneFrom(ts).prod;
  return ( true | it && t.prod == p | t <- ts );
}

private void flattenAmbs(Tree t, int depth, void(int, Tree,Tree) k) {
  if (t is hole) { //label(str name, _) := t.prod.def, /hole<named:[a-zA-Z0-9]*>/ := name) {
    // generate plug function here too.
    //k(makeHole(t.prod.def, t@\loc), t.args[0], Tree(Tree p) { return p });
    k(depth, makeHole(t.prod.def, t@\loc), t.args[0]); 
    return;
  }
  
  switch (t) {
    case appl(Production p, list[Tree] args): {
      for (int i <- [0..size(args)]) {
        //flattenAmbs(args[i], (Tree ctx, Tree redex, Tree(Tree) plug) {
        //k(appl(p, args[0..i] + [ctx] + args[i+1..])[@\loc=t@\loc], redex, Tree(Tree rt) {
        //   return appl(p, args[0..i] + plug(rt) + args[i+1..])[@\loc=t@\loc]
        // });
        flattenAmbs(args[i], depth + 1, (int d, Tree ctx, Tree redex) {
          k(d, appl(p, args[0..i] + [ctx] + args[i+1..])[@\loc=t@\loc], redex); 
        });
      }
    }
    
    case amb(set[Tree] alts): {
      //for (a <- alts) {
      //  println(a.prod);
      //}
      //if (allSameProd(alts)) {
        for (Tree a <- alts /*, !(a is hole)*/) {
          flattenAmbs(a, depth, (int d, Tree ctx, Tree redex) {
            k(d, ctx, redex);
          });
        }
      //} 
    }
  }
  
}
