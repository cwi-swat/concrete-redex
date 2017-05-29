module paper::ParseRedex

import ParseTree;
import List;
import Set;
import Type;
import IO;

extend paper::TraceRedex;


/*
 * Applying reduction relations
 */

alias CR = rel[Tree context, Tree reduct]; // context reduct pairs

RR apply(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules)
  = { <r, typeCast(#Tree, plug(tt, ctx2, rt))> |
    bprintln("STARTING REDUCTION"),  
     <&C ctx1, Tree rx> <- split(ct, t),
    //bprintln("redex = <rx>"),
     str r <- rules,
     //bprintln("RULE: <r>"), 
     <&C ctx2, Tree rt> <- red(r, ctx1, rx)
     , bprintln("<rx> === <r> ===\> <rt>")
      };


RR apply2(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules) {
  ctx = parse(ct, "<t>", t@\loc, allowAmbiguity=true);
  RR rr = {};
  flattenAmbs(ctx, (Tree alt, Tree rx) {
    rr +=  { <r, plug(tt, ctx2, rt)> | 
      str r <- rules, &C ctx1 := alt, 
      <&C ctx2, Tree rt> <- red(r, ctx1, rx), bprintln("<rx> === <r> ===\> <rt>") };
  });
  return rr;
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
    ctx = parse(ctxType, "<t>", t@\loc, allowAmbiguity=true);
  
    rel[Tree,Tree] toplevels = {};
    
    rel[Tree, Tree] result = {};
    flattenAmbs(ctx, (Tree alt, Tree redex) {
      // could we do the reductions here, without flattening it all?
      // (a kind of deforestation)
      if (alt is hole) {
        toplevels += {<alt, redex>};
      }
      else {
        result += {<alt, redex>};
      } 
    });
    if (result == {}) { // only add toplevels is no more nested stuff needs to be done;
      result += toplevels;
    }
    return result;
  }
  catch ParseError(loc _): {
    // stuck
    return {};
  }
}

@doc{Plug reduct back into context, turning it into a term}
&T plug(type[&T<:Tree] tt, Tree ctx, Tree reduct) {
  Tree t = visit (ctx) {
    case Tree h => reduct when h is hole
  };
  return parse(tt, "<t>");
}

private Tree makeHole(Symbol sym, loc l) 
  = appl(prod(label("hole", sym),[lit("☐")],{}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])])[@\loc=l];
 

//private void flattenAmbs2(Tree t, void(Tree,Tree, Tree(Tree, Tree)) k) {
//  if (t is hole) { //label(str name, _) := t.prod.def, /hole<named:[a-zA-Z0-9]*>/ := name) {
//    // generate plug function here too.
//    k(makeHole(t.prod.def, t@\loc), t.args[0], Tree(Tree ctx, Tree p) { return p; });
//    //k(makeHole(t.prod.def, t@\loc), t.args[0]); 
//    return;
//  }
//  
//  switch (t) {
//    case appl(Production p, list[Tree] args): {
//      for (int i <- [0..size(args)]) {
//        flattenAmbs2(args[i], (Tree ctx, Tree redex, Tree(Tree, Tree) plug) {
//           k(appl(p, args[0..i] + [ctx] + args[i+1..])[@\loc=t@\loc], redex, Tree(Tree myctx, Tree rt) {
//             return appl(p, myctx.args[0..i] + plug(args[i], rt) + myctx.args[i+1..])[@\loc=t@\loc];
//           });
//        });
//      }
//    }
//    
//    case amb(set[Tree] alts): {
//      for (Tree a <- alts) {
//        flattenAmbs2(a, (Tree ctx, Tree redex, Tree(Tree, Tree) plug) {
//          k(ctx, redex, plug);
//        });
//      } 
//    }
//  }
//  
//}

 
private void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (t is hole) { //label(str name, _) := t.prod.def, /hole<named:[a-zA-Z0-9]*>/ := name) {
    // generate plug function here too.
    //k(makeHole(t.prod.def, t@\loc), t.args[0], Tree(Tree p) { return p });
    k(makeHole(t.prod.def, t@\loc), t.args[0]); 
    return;
  }
  
  switch (t) {
    case appl(Production p, list[Tree] args): {
      for (int i <- [0..size(args)]) {
        //flattenAmbs(args[i], (Tree ctx, Tree redex, Tree(Tree) plug) {
        //k(appl(p, args[0..i] + [ctx] + args[i+1..])[@\loc=t@\loc], redex, Tree(Tree rt) {
        //   return appl(p, args[0..i] + plug(rt) + args[i+1..])[@\loc=t@\loc]
        // });
        flattenAmbs(args[i], (Tree ctx, Tree redex) {
          k(appl(p, args[0..i] + [ctx] + args[i+1..])[@\loc=t@\loc], redex); 
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
