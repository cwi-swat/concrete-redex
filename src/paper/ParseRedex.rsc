module paper::ParseRedex

import ParseTree;
import List;
import Type;
import IO;

extend paper::TraceRedex;


/*
 * Applying reduction relations
 */

alias CR = rel[Tree context, Tree reduct]; // context reduct pairs

R reduce(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules)
  = { typeCast(#Tree, plug(tt, ctx2, rt)) |  <ctx1, rx> <- split(ct, t),
     str r <- rules, <ctx2, rt> <- red(r, ctx1, rx) };

/*
 * Split and plug
 */

Tree plugCtx(type[&C<:Tree] ct, Tree ctx1, &C ctx2) {
  result = top-down-break visit (ctx1) {
    case &C t => ctx2 when t@\loc == ctx1@\loc
  }
  return result;
}

bool inHole(Tree t, Tree redex) = true
  when t is hole && t@\loc == redex@\loc;
  
bool inHole(t:appl(Production p, list[Tree] args), Tree redex) 
  = inHole(arg, redex)
  when 
    Tree arg <- args,  arg@\loc?, redex@\loc <= arg@\loc;
  

rel[Tree,Tree] split(type[&T<:Tree] ctxType, Tree t) {
  ctx = parse(ctxType, "<t>", t@\loc, allowAmbiguity=true);
  
  rel[Tree, Tree] result = {};
  flattenAmbs(ctx, (Tree alt, Tree redex) {
    result += {<alt, redex>};
  });
  
  return result;
}

&T plug(type[&T<:Tree] tt, Tree ctx, Tree reduct) {
  Tree t = visit (ctx) {
    case Tree h => reduct when h is hole
  };
  return parse(tt, "<t>");
}

private Tree makeHole(Symbol sym, loc l) 
  = appl(prod(label("hole", sym),[lit("☐")],{}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])])[@\loc=l];
 
private void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (t is hole) {
    k(makeHole(t.prod.def, t@\loc), t.args[0]); 
    return;
  }
  
  switch (t) {
    case appl(Production p, list[Tree] args): {
      for (int i <- [0..size(args)]) {
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
