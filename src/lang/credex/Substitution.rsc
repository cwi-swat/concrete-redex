module lang::credex::Substitution

import lang::credex::Resolve;

import ParseTree;
import String;
import List;
import IO;
import Type;
import util::Maybe;

/*
 * Generic, capture-avoiding substitution
 */

 
private int round = -1;

&T subst(type[&T<:Tree] tt, map[Tree, Tree] s, &T t, void(&T, Resolver) resolve) {
  round += 1;
  Resolver resolver = makeResolver(tt, resolve);
  resolver.resolve(t);
  //println("REFS: <resolver.refs()<use,decl>>");
  new = subst(s, t, resolver.refs());
  //println("NEW: <new>");
  ren = nameFix(tt, new, resolve);
  //println("REN: <ren>");
  if (ren != ()) { // prevent a traversal
    new = rename(new, ren);
  }
  return typeCast(tt, new);
}

Tree subst(map[Tree, Tree] s, Tree t, Refs refs) {
  if (Tree x <- s, boundIn(x, t, refs)) {
    return t;
  }

  // NB: == is modulo annos
  if (Tree x <- s, t == x) {
    Tree r = s[x];
    return r[@\loc=mark(r@\loc, round)];
  }

  if (appl(Production p, list[Tree] args) := t) {
    newArgs = [ i mod 2 == 0 ? subst(s, args[i], refs) : args[i] | int i <- [0..size(args)] ];
    Tree t2 = appl(p, newArgs);
    return t@\loc? ? t2[@\loc=t@\loc] : t2;
  }

  return t;
}

// t is in scope of a binding occurence of x
bool boundIn(Tree x, Tree t, Refs refs) 
  = t@\loc? && <loc def, Tree y, loc scope, def> <- refs 
      && scope == t@\loc && "<x>" == "<y>";

Tree rename(t:appl(Production p, list[Tree] args), map[loc, Tree] ren) {
  if (t@\loc?, t@\loc in ren, ren[t@\loc].prod == p) { 
    return ren[t@\loc];
  }
  t2 = appl(p, [ rename(a, ren) | Tree a <- args ]);
  if (t@\loc?) {
    t2 = t2[@\loc=t@\loc];
  }
  return t2;
}

default Tree rename(Tree t, map[loc, Tree] ren) = t; 
 
bool captured(loc use, loc decl)
  = getMark(use) == round && getMark(decl) != round;

map[loc,Tree] nameFix(type[&T<:Tree] tt, Tree t, void(&T, Resolver) resolve) { 
  captures = ();
  fv = {};
  
  rel[loc, loc] lookup_(Tree x, loc u, list[Env] envs) {
    for (Env env <- envs) {
      decls = { <s, d> | <s, d, x> <- env, !captured(u, d) };
      captures += ( d: x | <s, d, x> <- env, captured(u, d) );
      if (decls != {}) return decls; // else, go to next env
    }
    fv += {x}; // x is free
    return {}; 
  }

  Resolver resolver = makeResolver(tt, resolve, lookup = lookup_);
  resolver.resolve(t);
  refs = resolver.refs();  
  //println("NAMEFIX refs: <refs<use,decl>>");
  allNames = refs.name + fv; 

  map[loc, Tree] ren = ();  
  for (loc d <- captures) {
    new = fresh(captures[d], allNames);
    ren += ( occ: new | <loc occ, _, _, d> <- refs );
    allNames += {new};
  }
  return ren;
}

Tree fresh(Tree x, set[Tree] names) {
  // unfortunate, but the new names have different structure from parsed names
  // so need to do string comparison
  set[str] ns = { "<y>" | y <- names };
  
  while ("<x>" in ns) {
    x = appl(x.prod, x.args + [char(c) | int c <- chars("_") ])[@\loc=x@\loc];
  }
  return x;
}

