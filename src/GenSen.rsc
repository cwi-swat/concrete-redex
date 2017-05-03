module GenSen

import ParseTree;
import Type;
import util::Math;
import util::Maybe;
import List;
import String;
import IO;


list[Tree] genSens(type[&T<:Tree] typ, int bound, int depth) {
  set[Tree] result = {};

  int i = 0;
  while (i < bound) {
    genSen(typ, depth, (Tree t) {
      //if (t notin result) {
        result += {t};
        i += 1;
      //}
    });
  }

  return [ t | Tree t <- result ];
} 

void genSen(type[&T<:Tree] typ, int depth, void(Tree) k) 
  = genSen(typ.symbol, typ.definitions, depth, k);

void genSen(Symbol s, map[Symbol, Production] defs, int depth, void(Tree) k) {
  println("Visiting: <s> (depth = <depth>)");
  genSen_(s, defs, depth, k);
}

void genSen_(s:sort(_), map[Symbol, Production] defs, int depth, void(Tree) k)
  = genSen(defs[s].alternatives, defs, depth, k);

void genSen_(s:layouts(_), map[Symbol, Production] defs, int depth, void(Tree) k)
  //= genSen({ p | Production p <- defs[s].alternatives, \tag("category"("Comment")) notin p.attributes }, defs, depth, k);
  =  k(appl(p, [char(i) | int i <- chars(" ") ]))
  when Production p <- defs[s].alternatives;

void genSen_(s:lex(_), map[Symbol, Production] defs, int depth, void(Tree) k)
  = genSen(defs[s].alternatives, defs, depth, k);

Maybe[Production] smallest(list[Production] prods) {
  Maybe[Production] small = nothing();
  bool started = false;
  for (Production p <- prods) {
    if (!started) {
      small = just(p);
      started = true;
    }
    else {
      if (p is prod) {
        if (just(Production p2) := small, size(p.symbols) < size(p2.symbols)) {
          small = just(p);
        }
      }
      else if (p is priority) {
        maybeP2 = smallest([ a | choice(_, set[Production] ps) <- p.choices, Production a <- ps ]);
        if (just(Production p2) := maybeP2, just(Production p3) := small, size(p2.symbols) < size(p3.symbols)) {
          small = just(p);
        } 
      }
      else if (p is associativity) {
        ; // todo
      }
    }
  }
  return small;
}

void genSen(set[Production] alts, map[Symbol, Production] defs, int depth, void(Tree) k) {

  list[Production] prods = [ p | Production p <- alts ];

  assert size(prods) > 0: "Sort with no productions"; 

  Production p;
  if (depth <= 0, just(Production sm) := smallest(prods)) { 
    p = sm;
  }
  else {
    int pick = arbInt(size(prods));
    p = prods[pick];
  }


  if (p is regular) {
    genSen(p.def, defs, depth, k);
    return;
  }
  
  if (p is priority) {
    // for now, ignoring actual prio
    genSen({ a | choice(_, set[Production] ps) <- p.choices, Production a <- ps } , defs, depth, k);
    return;
  }
  
  // \associativity(Symbol def, Associativity \assoc, set[Production] alternatives) 
  if (p is associativity) {
    throw "not implemented";
  }

  list[Tree] args = [];
  for (Symbol sym <- p.symbols) {
    genSen(sym, defs, depth - 1, (Tree a) {
      args += [a];
    });
  }
  k(appl(p, args));
}

void genSen_(reg:\empty(), map[Symbol, Production] defs, int depth, void(Tree) k)
  = genSen(reg, [], defs, depth, k);

void genSen_(reg:\alt(set[Symbol] syms), map[Symbol, Production] defs, int depth, void(Tree) k) {
  lsyms = [ s | Symbol s <- syms ];
  genSen(reg, [ lsyms[arbInt(size(lsyms))] ], defs, depth, k);
}

void genSen_(reg:\opt(Symbol s), map[Symbol, Production] defs, int depth, void(Tree) k) {
  int len = depth <= 0 ? 0 : arbInt(2);
  genSen(reg, [ s | int _ <- [0..len] ], defs, depth, k);
}

void genSen_(reg:\seq(list[Symbol] syms), map[Symbol, Production] defs, int depth, void(Tree) k)
  = genSen(reg, syms, defs, depth, k);

void genSen_(reg:\iter(Symbol s), map[Symbol, Production] defs, int depth, void(Tree) k) {
  int len = depth <= 0 ? 1 : 1 + arbInt(10);
  genSen(reg, [ s | int _ <- [0..1 + arbInt(10)] ], defs, depth, k);
}

void genSen_(reg:\iter-star(Symbol s), map[Symbol, Production] defs, int depth, void(Tree) k) {
  int len = depth <= 0 ? 0 : arbInt(10);
  genSen(reg, [ s | int _ <- [0..len] ], defs, depth, k);
}

void genSen_(reg:\iter-seps(Symbol sym, list[Symbol] seps), map[Symbol, Production] defs, int depth, void(Tree) k) {
  int len = depth <= 0 ? 1 : max(1,  arbInt(5) * (1 + size(seps)) - size(seps));
  list[Symbol] seq = [sym, *seps];
  allSyms = [ seq[i % (1 + size(seps))] | int i <- [0..len] ];
  //println("ALLSYMS for <len> iter-steps: <allSyms>");
  genSen(reg, allSyms, defs, depth, k);
}

void genSen_(reg:\iter-star-seps(Symbol sym, list[Symbol] seps), map[Symbol, Production] defs, int depth, void(Tree) k) {
  int len = depth <= 0 ? 0 : max(0,  arbInt(5) * (1 + size(seps)) - size(seps));
  list[Symbol] seq = [sym, *seps];
  allSyms = [ seq[i % (1 + size(seps))] | int i <- [0..len] ];
  //println("ALLSYMS for <len> iter-star-steps: <allSyms>");
  genSen(reg, allSyms, defs, depth, k);
}

void genSen(Symbol s, list[Symbol] syms, map[Symbol, Production] defs, int depth, void(Tree) k) {
  list[Tree] args = [];

  for (Symbol sym <- syms) {
    genSen(sym, defs, depth - 1, (Tree a) {
      args += [a];
    });
  }
  k(appl(regular(s), args));
}

void genSen_(\conditional(Symbol s, _), map[Symbol, Production] defs, int depth, void(Tree) k) 
  = genSen(s, defs, depth, k);

void genSen_(\lit(str l), map[Symbol, Production] defs, int depth, void(Tree) k) {
  k(appl(prod(\lit(l), [], {}), [ char(i) | int i <- chars(l) ]));
}

void genSen_(\cilit(str l), map[Symbol, Production] defs, int depth, void(Tree) k) {
  k(appl(prod(\cilit(l), [], {}), [ char(i) | int i <- chars(l) ]));
}

void genSen_(\char-class(list[CharRange] rs), map[Symbol, Production] defs, int depth, void(Tree) k) {
  int pick = arbInt(size(rs));
  CharRange picked = rs[pick];
  int ch = picked.begin + arbInt(max(1, picked.end - picked.begin));
  Tree c = char(ch);
  k(c);
}


