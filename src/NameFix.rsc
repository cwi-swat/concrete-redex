module NameFix

import ParseTree;
import IO;
import List;

alias Index = rel[loc, Tree];

// to be extended
default Tree prime(Tree t) = t;

default Refs resolve(Tree _, list[Env] _, Lookup _) = {};

default Tree subst(Tree t, Tree x, Tree e) = t;


//////


alias Env = rel[Tree name, loc decl, loc scope];


// start of list = inner
alias Scope = list[Env];
alias Refs = rel[loc use, loc def, Tree name];
alias Lookup = set[loc](Tree, loc, Scope);
alias GetRenaming = map[loc,Tree](Refs);  


Tree fresh(Tree x, set[Tree] names) {
  while (x in names) {
    x = prime(x);
  }
  return x;
}


&T doSubst(type[&T<:Tree] typ, &T t, Tree x, Tree sub) {
  t = subst(t, x, sub);
  <lu, getRenaming> = makeResolver();
  refs = resolve(t, [], lu);
  renaming = getRenaming(refs);

  Tree t2 = visit (t) {
    case Tree z => renaming[z@\loc]
      when z@\loc?, z@\loc in renaming
  };

  if (&T typed := t2) {
    return typed;
  }
}

tuple[Lookup, GetRenaming] makeResolver() {
  map[loc, Tree] toRename = ();
  
  set[loc] lookup__(Tree name, loc use, Scope sc) {
    for (Env env <- sc, <name, loc def, loc scope> <- env) {
      if (use <= scope) { //contains(scope, use)) {
        return {def};
      }
      // captures are renamed until a non-capturing decl is found
      toRename[def] = name;
    }
    // not found
    return {};
  }
  
  map[loc, Tree] getRenaming__(Refs refs) {
    ren = ();
    set[Tree] allNames = refs<2>;
    for (loc d <- toRename) {
      Tree n = fresh(toRename[d], allNames);
      //println("Fresh: <n>");
      allNames += {n};
      ren[d] = n;
      ren += ( u: n | <loc u, d, _> <- refs ); 
    }
    return ren;
  }

  return <lookup__, getRenaming__>;
}

