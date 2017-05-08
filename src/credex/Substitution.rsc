module credex::Substitution

import ParseTree;
import IO;
import List;

alias Env = rel[Tree name, loc decl, loc scope];
alias Scope = list[Env];
alias Refs = rel[loc use, loc def, Tree name];
alias Lookup = set[loc](Tree, loc, Scope);
alias GetRenaming = map[loc,Tree](Refs);  


&T substitute(type[&T<:Tree] termType, type[&V<:Tree] varType, type[&R<:Tree] replaceType, &T t, &V x, &R sub,
   &T(&T, &V, &R) mySubst, Refs(&T, Scope, Lookup) myResolve, &V(&V) myPrime) {
  &T newT = mySubst(t, x, sub);
  <lu, getRenaming> = makeResolver(varType, myPrime);
  refs = myResolve(newT, [], lu);
  renaming = getRenaming(refs);

  &T renamedT = visit (newT) {
    case Tree z => renaming[z@\loc]
      when z@\loc?, z@\loc in renaming
  };

  return renamedT;
}

private &T fresh(type[&T<:Tree] varType, &T x, set[&T] names, &T(&T) myPrime) {
  while (x in names) {
    x = myPrime(x);
  }
  return x;
}


private tuple[Lookup, GetRenaming] makeResolver(type[&T<:Tree] varType, &T(&T) myPrime) {
  map[loc, Tree] toRename = ();
  
  set[loc] lookup__(Tree name, loc use, Scope sc) {
    for (Env env <- sc, <name, loc def, loc scope> <- env) {
      if (use <= scope) { // non-containment = capture (?)
        return {def};
      }
      // captures are renamed until a non-capturing decl is found
      toRename[def] = name;
    }
    // not found
    return {};
  }
  
  map[loc, Tree] getRenaming__(Refs refs) {
    map[loc, Tree] ren = ();
    set[Tree] allNames = refs<2>;
    for (loc d <- toRename) {
      Tree n = fresh(varType, toRename[d], allNames, myPrime);
      allNames += {n};
      ren[d] = n;
      ren += ( u: n | <loc u, d, _> <- refs ); 
    }
    return ren;
  }

  return <lookup__, getRenaming__>;
}

