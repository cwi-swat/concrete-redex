module lang::credex::Substitution

import ParseTree;
import String;
import List;
import IO;
import Type;
import util::Maybe;

/*
 * Generic, capture-avoiding substitution
 */

alias Env = rel[loc scope, loc decl, Tree name];
alias Lookup = rel[loc scope, loc decl](Tree, loc, list[Env]);
alias Refs = rel[loc use, Tree name, loc scope, loc decl];
alias Resolver[&T] = Refs(&T, list[Env], Lookup); 

 
private int round = -1;

&T subst(type[&T<:Tree] tt, Tree x, Tree r, &T t, Resolver[&T] resolve, bool fix = true) {
  round += 1;
  new = subst(x, r, t, resolve(t, [], defaultLookup));
  return typeCast(tt, fix ? rename(new, nameFix(new, resolve)) : new);
}

Tree subst(Tree x, Tree r, Tree t, Refs refs) {
  if (boundIn(x, t, refs)) return t;

  // NB: == is modulo annos
  if (t == x) return mark(r, round);

  if (appl(Production p, list[Tree] args) := t) {
    Tree t2 = appl(p, [ subst(x, r, a, refs) | a <- args ]);
    if (t@\loc?) { // this is ugly...
      t2@\loc = t@\loc;
    }
    return t2;
  }

  return t;
}

private rel[loc, loc] defaultLookup(Tree x, loc u, list[Env] envs) {
  for (Env env <- envs) {
    decls = {<s, d> | <s, d, x> <- env };
    if (decls != {}) return decls;
  }
  return {}; // not found
}

private int getMark(loc l) = l.fragment != "" ? toInt(l.fragment) : -1;

private Tree mark(t:appl(Production p, list[Tree] args), int round) {
  if (t@\loc?) {
    return appl(p, [ mark(a, round) | Tree a <- args ])[@\loc=t@\loc[fragment="<round>"]];
  } 
  return t;
}

private default Tree mark(Tree t, int round) = t;

private Tree mark_slow(Tree t, int round) {
  return visit (t) {
    case Tree x => x[@\loc = x@\loc[fragment = "<round>"]] when x@\loc? 
  }
}

// t is in scope of a binding occurence of x
bool boundIn(Tree x, Tree t, Refs refs) 
  = t@\loc? && <loc def, Tree y, loc scope, def> <- refs 
      && scope == t@\loc && "<x>" == "<y>";

// rename all variable occurences according to ren
Tree rename(Tree t, map[loc,Tree] ren) {
 return visit (t) {
    case Tree x => ren[x@\loc] 
      when x@\loc?, x@\loc in ren, 
        ren[x@\loc].prod == x.prod // needed because injections
  };
}
 
bool captured(loc use, loc decl)
  = getMark(use) == round && getMark(decl) != round;

map[loc,Tree] nameFix(&T<:Tree t, Resolver[&T] resolve) { 
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

  refs = resolve(t, [], lookup_);  
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

