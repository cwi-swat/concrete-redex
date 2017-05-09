module credex::Substitution

import ParseTree;
import IO;
import List;
import String;
import util::Maybe;

//alias Env = rel[Tree name, loc decl, loc scope];
alias Env = rel[loc scope, loc decl, Tree name];
//alias Refs = rel[loc scope, loc use, loc def, Tree name];
alias Refs = rel[loc use, Tree name, loc scope, loc decl];

alias Scope = list[Env];
alias Lookup = rel[loc, loc](Tree, loc, Scope);
alias GetRenaming = map[loc,Tree](Refs);  
alias Resolver = tuple[Lookup lookup, GetRenaming getRenaming];

@doc{This global variable represents phases of substitution.
Every substitute call increases the round, so that newly
inserted subterms can be distinguished from earlier ones. }
private int round = -1;


@doc{Call `replace` in your syntactic substitution functions
when actually inserting the substituant into the term. This
supports name capture detection in the `substitute` drive function.}
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

Tree replace(Tree t) {
  t = visit (t) {
    case Tree tz => tz[@\loc = tz@\loc[fragment = "<round>"]]
      when tz@\loc? 
  }
  return t;  
}



Tree traverseSubst(type[&T<:Tree] typ, type[&V<:Tree] varType, 
  Maybe[&T](&T, &V, &T) doit, Tree subj, &V var, &T exp, Refs refs) {
  if (&T tsubj := subj, just(Tree x) := doit(tsubj, var, exp)) {
    return replace(exp);
  }
  if (subj@\loc?, loc scope := subj@\loc, <loc def, var, scope, def> <- refs) {
    return subj;
  } 
  if (appl(_, _) := subj) {
    Tree t2 = appl(subj.prod, [ traverseSubst(typ, varType, doit, a, var, exp, refs) | Tree a <- subj.args ]);
    if (subj@\loc?) {
     t2@\loc = subj@\loc;
    }
    return t2;
  }
  return subj;
}

@doc{Capture-avoiding substitution. This function uses the provided syntactic
substitution function `mySubst` and custom name resolution function `myResolve`
to fix name capturing after substitution has taken place. Function `myPrime`
is used to produce new names.}
&T substitute(type[&T<:Tree] termType, type[&V<:Tree] varType, type[&R<:Tree] replaceType, &T t, &V x, &R sub,
   Maybe[&R](&R, &V, &R) mySubst, Refs(&T, Scope, Lookup) myResolve, &V(&V) myPrime) {
  round += 1;
  println("Round = <round>");
  Resolver resolver = makeResolver(varType, myPrime);
  Refs refs = myResolve(t, [], resolver.lookup);

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
}


@doc{Capture-avoiding substitution. This function uses the provided syntactic
substitution function `mySubst` and custom name resolution function `myResolve`
to fix name capturing after substitution has taken place. Function `myPrime`
is used to produce new names.}
&T substitute_(type[&T<:Tree] termType, type[&V<:Tree] varType, type[&R<:Tree] replaceType, &T t, &V x, &R sub,
   &T(&T, &V, &R) mySubst, Refs(&T, Scope, Lookup) myResolve, &V(&V) myPrime) {
  round += 1;
  println("Round = <round>");
  &T newT = mySubst(t, x, sub);
  // TODO:
  // resolve t
  // find x in t, if it's a def (e.g., <x@\loc, x@\loc, x> <- refs)
  // then don't go into term? This requires scope...
  
  // if a terms @loc represents a scope, and it defines an x
  // don't traverse it further
  Resolver resolver = makeResolver(varType, myPrime);
  refs = myResolve(newT, [], resolver.lookup);
  //for (<a, b, c> <- refs) {
  //  println("REF: <a>, <b>, <c>");
  //}
  renaming = resolver.getRenaming(refs);

  &T renamedT = visit (newT) {
    case Tree z => renaming[z@\loc]
      when z@\loc?, z@\loc in renaming
  };

  return renamedT;
}

@doc{Compute set of free variables according to provided resolve function.}
set[&V] freeVars(type[&T<:Tree] termType, type[&V<:Tree] varType, &T t, 
  Refs(&T, Scope, Lookup) myResolve) {
  fv = {};
  
  rel[loc, loc] lu(Tree name, loc use, Scope sc) {
    if (Env env <- sc, <name, loc def, _> <- env, !isCapture(use, def)) {
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

