module paper::MatchRedex

import credex::Matching;
import ParseTree;
import Node;
import Type;

extend paper::TraceRedex;


alias CR = rel[node, Tree];

R reduce(type[&C<:node] ct, CR(str,&C) red, &T<:Tree t, set[str] rules, type[node] cts...)
  = { plug(ctx2, rt, t) |  ctx1 <- split(ct, t, cts), 
        str r <- rules, <ctx2, rt> <- red(r, ctx1) };

        
node plugCtx(node ctx1, node ctx2) {
  loc origin(node n) = typeCast(#loc, getKeywordParameters(n)["src"]);
    
  return top-down-break visit (ctx1) {
    case Tree _: ;
    case node n => ctx2
      when origin(n) == origin(ctx2)
  }
}
        