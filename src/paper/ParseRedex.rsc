module paper::ParseRedex

import ParseTree;
import String;
import List;
import IO;
import Type;
import util::Maybe;

extend paper::TraceRedex;


/*
 * Applying reduction relations
 */

alias CR = rel[Tree context, Tree redex]; // context reduce pairs

R reduce(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C,Tree) red, &T t, set[str] rules)
  = { typeCast(#Tree, plug(tt, ctx2, rt)) |  <ctx1, rx> <- split(ct, t), //bprintln(ctx1), bprintln(rx), 
     str r <- rules,
     //bprintln("trying [<r>] on <rx>]"),
      <ctx2, rt> <- red(r, ctx1, rx)
      //bprintln("success: <rt>") 
    };

/*
 * Split and plug
 */

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

private Tree makeHole(Symbol sym) 
  = appl(prod(label("hole", sym),[lit("☐")],{}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
 
private void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (t is hole) {
    k(makeHole(t.prod.def), t.args[0]); // skip over "hole" injection
    return;
  }
  
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
