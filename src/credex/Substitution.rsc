module credex::Substitution

import ParseTree;
import IO;
import List;
import String;
import util::Maybe;

alias Env = rel[loc scope, loc decl, Tree name];

alias Refs = rel[loc use, Tree name, loc scope, loc decl];

alias Scope = list[Env];

alias Lookup = rel[loc, loc](Tree, loc, Scope);

alias GetRenaming = map[loc,Tree](Refs);  

alias Resolver = tuple[Lookup lookup, GetRenaming getRenaming];

@doc{This global variable represents phases of substitution.
Every substitute call increases the round, so that newly
inserted subterms can be distinguished from earlier ones. }
private int round = -1;

@doc{Mark all terms in `t` to be from this substitution round.} 
private Tree replace(Tree t) {
  t = visit (t) {
    case Tree tz => tz[@\loc = tz@\loc[fragment = "<round>"]]
      when tz@\loc? 
  }
  return t;  
}


@doc{Recursively traverse a term, and apply substitutions throughout,
except when a term is a scope that bindgs `var`.}
private Tree traverseSubst(type[&T<:Tree] typ, type[&V<:Tree] varType, 
  Maybe[&T](&T, &V, &T) doit, Tree subj, &V var, &T exp, Refs refs) {
  
  if (subj@\loc?, loc scope := subj@\loc, <loc def, var, scope, def> <- refs) {
    // subject is a binder of var; don't continue.
    return subj;
  } 
  
  if (&T tsubj := subj, just(Tree x) := doit(tsubj, var, exp)) {
    // we have found the variable
    return replace(exp);
  }

  if (appl(_, _) := subj) {
    // do the recursion
    Tree t2 = appl(subj.prod, [ traverseSubst(typ, varType, doit, a, var, exp, refs) | Tree a <- subj.args ]);
    if (subj@\loc?) {
     t2@\loc = subj@\loc;
    }
    return t2;
  }
  
  // otherwise, return unchanged.
  return subj;
}

@doc{Capture-avoiding substitution. This function uses the provided syntactic
substitution function `mySubst` and custom name resolution function `myResolve`
to fix name capturing after substitution has taken place. Function `myPrime`
is used to produce new names.}
&T substitute(type[&T<:Tree] termType, type[&V<:Tree] varType, type[&R<:Tree] replaceType, &T t, &V x, &R sub,
   Maybe[&R](&R, &V, &R) mySubst, Refs(&T, Scope, Lookup) myResolve, &V(&V) myPrime) {
  round += 1;

  rel[loc, loc] lu(Tree name, loc use, Scope sc) {
    if (Env env <- sc, <loc scope, loc def, name> <- env) {
      return {<scope, def>};
    }
    return {};
  }
  
  Refs refs = myResolve(t, [], lu);

  if (&T newT := traverseSubst(replaceType, varType, mySubst, t, x, sub, refs)) {
    Resolver resolver = makeResolver(varType, myPrime);
    Refs refs = myResolve(newT, [], resolver.lookup);
    renaming = resolver.getRenaming(refs);
  
    &T renamedT = visit (newT) {
      case Tree z => renaming[z@\loc]
        when z@\loc?, z@\loc in renaming
    };
    return renamedT;
  }
  
  assert false: "traverseSubst not type-preserving!";
}


@doc{Compute set of free variables according to provided resolve function.}
set[&V] freeVars(type[&T<:Tree] termType, type[&V<:Tree] varType, &T t, 
  Refs(&T, Scope, Lookup) myResolve) {
  fv = {};
  
  rel[loc, loc] lu(Tree name, loc use, Scope sc) {
    if (Env env <- sc, <_, loc def, name> <- env, !isCapture(use, def)) {
      ; // we found a definition, so *not* free.
    }
    else {
      fv += { v | &V v := name };
    }
    return {};
  } 
    
  myResolve(t, [], lu);
  
  return fv;
}

@doc{Obtain a fresh name relative to the set `names`. The function
`myPrime` is used to create new names.}
&T fresh(type[&T<:Tree] varType, &T x, set[&T] names, &T(&T) myPrime) {
  while (x in names) {
    x = myPrime(x);
  }
  return x;
}

@doc{Determine whether the `use` of a name is captured by definition `def`.
A use is captured its `round` (as encoded in the location fragment) is the
current round, but the round of `def` is absent or less than it.}
private bool isCapture(loc use, loc def) 
  = use.fragment == "<round>" && def.fragment != "<round>";

private Resolver makeResolver(type[&T<:Tree] varType, &T(&T) myPrime) {
  map[loc, Tree] toRename = ();
  
  rel[loc, loc] lookup__(Tree name, loc use, Scope sc) {
    //println("lookup of <name> at <use>");
    for (Env env <- sc, <loc scope, loc def, name> <- env) {
      if (!isCapture(use, def)) { 
        //println("No Capture");
        return {<scope, def>};
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
    set[Tree] allNames = refs.name;
    for (loc d <- toRename) {
      Tree n = fresh(varType, toRename[d], allNames, myPrime);
      allNames += {n};
      ren[d] = n;
      ren += ( u: n | <loc u, _, _, d> <- refs ); 
    }
    return ren;
  }

  return <lookup__, getRenaming__>;
}

