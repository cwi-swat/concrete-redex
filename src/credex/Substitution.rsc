module credex::Substitution

import ParseTree;
import IO;
import List;
import String;

alias Env = rel[Tree name, loc decl];
alias Scope = list[Env];
alias Refs = rel[loc use, loc def, Tree name];
alias Lookup = set[loc](Tree, loc, Scope);
alias GetRenaming = map[loc,Tree](Refs);  

private int round = -1;

&T replace(type[&T<:Tree] ty, &T t) {
  Tree t0 = t;
  
  t0 = visit (t0) {
    case Tree tz => tz[@\loc = tz@\loc[fragment = "<round>"]]
      when tz@\loc? 
  }
  
  if (&T t2 := t0) {
    return t2;
  }
}

&T substitute(type[&T<:Tree] termType, type[&V<:Tree] varType, type[&R<:Tree] replaceType, &T t, &V x, &R sub,
   &T(&T, &V, &R) mySubst, Refs(&T, Scope, Lookup) myResolve, &V(&V) myPrime) {
  round += 1;
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

bool isCapture(loc use, loc def) {
  r1 = def.fragment;
  r2 = use.fragment;
  //println("Use: <use>");
  //println("Def: <def>");
  //println("r1: <r1>, r2: <r2>");
  if (r1 == r2) {
    return false;
  }  
  if (r1 == "", toInt(r2) == round) {
    return true;
  }
  if (r1 != "", toInt(r1) < round, toInt(r2) == round) {
    return true;
  }
  return false;
}


private tuple[Lookup, GetRenaming] makeResolver(type[&T<:Tree] varType, &T(&T) myPrime) {
  map[loc, Tree] toRename = ();
  
  set[loc] lookup__(Tree name, loc use, Scope sc) {
    for (Env env <- sc, <name, loc def> <- env) {
      if (!isCapture(use, def)) { 
        //println("No Capture");
        return {def};
      }
      //println("Capture");
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

