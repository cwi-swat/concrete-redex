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
private Tree traverseSubst(Tree subj, Tree var, Tree exp, Refs refs) {
  
  if (subj@\loc?, loc scope := subj@\loc, <loc def, var, scope, def> <- refs) {
    // subject is scope of a binder of var; don't continue.
    return subj;
  } 
  
  if (subj == var) {
    // &T tsubj := subj, just(Tree x) := doit(tsubj, var, exp)) {
    // we have found the variable
    return replace(exp);
  }

  if (appl(Production p, list[Tree] args) := subj) {
    // do the recursion
    Tree t2 = appl(p, [ traverseSubst(a, var, exp, refs) | Tree a <- args ]);
    return subj@\loc? ? t2[@\loc=subj@\loc] : t2;
  }
  
  // otherwise, return unchanged.
  return subj;
}

Refs justResolve(type[&T<:Tree] typ, &T t, Refs(&T, Scope, Lookup) myResolve) {
  rel[loc, loc] lu(Tree name, loc use, Scope sc) 
    = { <scope, def> | Env env <- sc, <loc scope, loc def, name> <- env };
  return myResolve(t, [], lu);
}

map[loc, Tree] namePatch(type[&T<:Tree] typ, type[&T<:Tree] varType, &T t, 
   Refs(&T, Scope, Lookup) myResolve) {

   Resolver resolver = makeResolver(varType);
   Refs refs = myResolve(t, [], resolver.lookup);

   return resolver.getRenaming(refs);
}

&T rename(type[&T<:Tree] typ, &T term, map[loc, Tree] renaming) {
  return visit (term) {
    case Tree t => renaming[t@\loc]
      when t@\loc?, t@\loc in renaming
  };
}

@doc{Capture-avoiding substitution. This function uses the provided syntactic
substitution function `mySubst` and custom name resolution function `myResolve`
to fix name capturing after substitution has taken place. Function `myPrime`
is used to produce new names.}
&T substitute(type[&T<:Tree] termType, type[&V<:Tree] varType, type[&R<:Tree] replaceType, &T t, &R x, &R sub,
   Refs(&T, Scope, Lookup) myResolve) {
  round += 1;
  
  // resolve the term, so that traverseSubst knows 
  // the scope of binders to guide the substitution.
  Refs refs = justResolve(termType, t, myResolve);

  if (&T newT := traverseSubst(t, x, sub, refs)) {
    map[loc, Tree] renaming = namePatch(termType, varType, newT, myResolve);
    return rename(termType, newT, renaming);
  }
  
  assert false: "traverseSubst not type-preserving!";
}


@doc{Compute set of free variables according to provided resolve function.}
set[&V] freeVars(type[&T<:Tree] termType, type[&V<:Tree] varType, &T t, 
  Refs(&T, Scope, Lookup) myResolve) {
  fv = {};
  
  rel[loc, loc] lu(Tree name, loc use, Scope sc) {
    if (Env env <- sc, <_, loc def, name> <- env, !isCapture(use, def)) {
      return {}; // we found a definition, so *not* free.
    }
    fv += { v | &V v := name };
  } 
    
  myResolve(t, [], lu);
  
  return fv;
}

@doc{Derive a new name from `x`.}
&T prime(type[&T<:Tree] varType, &T x) 
  = y
  when 
    appl(Production p, list[Tree] args) := x,
    &T y := appl(p, args + [char(95)]);

//TODO: this doesn't work because of the reified type/parsing bug
//&T prime(type[&T<:Tree] varType, &T x) = parse(varType, "<x>_");
  
@doc{Obtain a fresh name relative to the set `names`. The function
`myPrime` is used to create new names.}
&T fresh(type[&T<:Tree] varType, &T x, set[&T] names) {
  while (x in names) {
    x = prime(varType, x);
  }
  return x;
}

@doc{Determine whether the `use` of a name is captured by definition `def`.
A use is captured its `round` (as encoded in the location fragment) is the
current round, but the round of `def` is absent or less than it.}
private bool isCapture(loc use, loc def) 
  = use.fragment == "<round>" && def.fragment != "<round>";

private Resolver makeResolver(type[&T<:Tree] varType) {
  map[loc, Tree] toRename = ();
  
  rel[loc, loc] lookup__(Tree name, loc use, Scope sc) {
    for (Env env <- sc, <loc scope, loc def, name> <- env) {
      if (!isCapture(use, def)) { 
        // TODO: return all non-capturing defs in single scope (?)
        return {<scope, def>};
      }
      // captures are renamed until a non-capturing decl is found
      toRename[def] = name;
    }
    // not found
    return {};
  }
  
  // TODO: maybe there's a little too much logic in this local function
  // the only essential thing is the toRename map.
  map[loc, Tree] getRenaming__(Refs refs) {
    map[loc, Tree] ren = ();
    // TODO: allnames does not include free vars, is that a problem?
    set[Tree] allNames = refs.name; 
    for (loc d <- toRename) {
      Tree n = fresh(varType, toRename[d], allNames);
      allNames += {n};
      ren[d] = n;
      ren += ( u: n | <loc u, _, _, d> <- refs ); 
    }
    return ren;
  }

  return <lookup__, getRenaming__>;
}

