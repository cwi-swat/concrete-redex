module NameFix

import ParseTree;
import IO;
import List;

alias Index = rel[loc, Tree];

// to be extended
default Tree prime(Tree t) = t;

default set[Tree] getNames(Tree _) = {};

default Tree subst(t:appl(Production p, list[Tree] args), Tree var, Tree exp) 
  = t@\loc? ? appl(p, [ subst(a, var, exp) | Tree a <- t.args ])[@\loc=t@\loc]
      : appl(p, [ subst(a, var, exp) | Tree a <- t.args ]);
  
default Tree subst(Tree t, Tree var, Tree exp) = t;

//////


tuple[Tree,set[Tree]] fresh(Tree x, set[Tree] names) {
  while (x in names) {
    //println("RENAMING!!! <x>");
    x = prime(x);
    //println("PRIMED ----\> <x>");
  }
  return <x, names + {x}>;
}

Tree substitute(Tree t, map[loc,Tree] ren) {
  return visit (t) {
    case Tree x => ren[x@\loc]
      when x@\loc?, x@\loc in ren
  }
}


int round = 0;

// Maybe have drive "subst" that calls user subst
// checks if any subterm is replaced, then automatically
// calls mark. recursive function.

private Tree mark(Tree t) {
  t@\loc.query = "<round>";
  return t;
} 

&T doSubst(type[&T<:Tree] typ, &T t, Tree var, Tree exp) {
  t = subst(t, var, mark(exp));
  t = propagate(t, round, false);
  t = fix(t, namesOf(t), round);
  round += 1; // this should be outside (part of RRedex reduction cycle), since scope is not 1 substitution
  if (&T typed := t) {
    return typed;
  }
  assert false: "could make typed term";
}

// TODO: merge propaget with namesOf
private Tree propagate(Tree t, int round, bool doIt) {
  //println("Propagating <t> (round = <round>, doit = <doIt>)");
  if (!t@\loc?) {
    //println("No loc for <t>");
    return t;
  }
  
  //println("LOC = <t@\loc>");
  //if (!(t is appl)) {
  if (appl(_, _) !:= t) {
    //println("Not an appl: <t>");
    return t;
  }
  
  if (doIt) {
    //println("setting round = <round>");
    t@\loc.query = "<round>";
  }

  return appl(t.prod, [ propagate(arg, round, t@\loc.query == "<round>" || doIt) | Tree arg <- t.args ])[@\loc=t@\loc];
}

Index namesOf(Tree t) 
  = { <name@\loc, name> | /Tree sub := t, Tree name <- getNames(sub), name@\loc? };

Tree fix(Tree gen, Index names, int round) {
  //println("ROUND = <round>");
  bool isNew(Tree x) = x@\loc.query == "<round>"; 
  
  set[Tree] other = { x | <_, Tree x> <- names, isNew(x) }; 

  set[Tree] allNames = { x | <_, Tree x> <- names }; 
  
  map[loc,Tree] subst = ();
  map[Tree, Tree] renaming = ();

  // NB: this depends on the fact that equals is modulo annos
  for (<loc l, Tree x> <- names, !isNew(x), x in other) {
    //println("Checking <l>: <x>");
    if (x notin renaming) {
      <y, allNames> = fresh(x, allNames);
      //println("YYYY = <y>"); 
      renaming[x] = y;
    }
    subst[l] = renaming[x]; 
  }
  
  return substitute(gen, subst); 
}
