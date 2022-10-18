module lang::credex::util::Filter

import ParseTree;

import lang::rascal::grammar::definition::Priorities;
import Grammar;
import IO;


Production unContext(Production p) {
  return visit (p) {
    case sort("E") => sort ("Expr")
  }
}

DoNotNest getPrios(type[&T<:Tree] t) = doNotNest(grammar({}, t.definitions));

// the goal is disambiguate according to
// prios, but modular E vs Expr renaming.

&T filterBadContexts(type[&T<:Tree] typ, type[&E<:Tree] org,  &T ctx, DoNotNest prios) {
  
  return visit (ctx) {
    case amb(set[Tree] alts): {
      // each alt is a potential parent
      for (alt:appl(Production pprod, list[Tree] pargs) <- alts) {
        println("Trying to filter: <alt>");
        for (kid:appl(Production kprod, list[Tree] kargs) <- pargs) {
          pprod2 = unContext(pprod);
          kprod2 = unContext(kprod);
          if (<Production pprodOrg, int pos, Production kprodOrg> <- prios
              , pprodOrg.def == pprod2.def, pprodOrg.symbols == pprod2.symbols
              , kprodOrg.def == kprod2.def, kprodOrg.symbols == kprod2.symbols 
              , pargs[pos] == kid) {
            println("Filtered: <alt> vs <kid>");
            alts -= {alt};
          }
          // todo: this needs to be transitively done
          // *any* chain of injections counts
          if (/prod(Symbol def, [Symbol injected], _) := org,
            <Production pprodOrg, int pos, Production kprodOrg> <- prios
              , pprodOrg.def == pprod2.def, pprodOrg.symbols == pprod2.symbols
              , kprodOrg.def == kprod2.def, kprodOrg.symbols == kprod2.symbols 
              , pargs[pos] == kid) {
            println("Filtered: <alt> vs <kid>");
            alts -= {alt};        
          }
          // Expr = Num
          // if there is an injection from something in the ctx
          // to an NT for which the above property holds, also filter           
        }
      }
      if ({Tree t} := alts) {
        insert t;
      }
      else {
        insert amb(alts);
      }
    }
  }
}