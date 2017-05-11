module credex::Substitution

import ParseTree;
import IO;
import List;
import String;
import Type;
import util::Maybe;


alias Env = rel[loc scope, loc decl, Tree name];

alias Refs = rel[loc use, Tree name, loc scope, loc decl];

alias Scope = list[Env];

alias Lookup = rel[loc scope, loc decl](Tree, loc, Scope);

alias Resolver = tuple[Lookup lookup, map[loc,Tree]() captures];

@doc{This global variable represents phases of substitution.
Every substitute call increases the round, so that newly
inserted subterms can be distinguished from earlier ones. }
private int round = -1;

@doc{Determine whether the `use` of a name is captured by definition `def`.
A use is captured its `round` (as encoded in the location fragment) is the
current round, but the round of `def` is absent or less than it.}
private bool isCapture(loc use, loc def) 
  = use.fragment == "<round>" && def.fragment != "<round>";

@doc{Capture-avoiding substitution. This function the provided custom name 
resolution function `resolve` to fix name capturing after substitution has
taken place.}
&T substitute(
  type[&T<:Tree] termType, // the top term type (e.g. #Prog, #Expr)
  type[&V<:Tree] varType,  // the type of vars (e.g. #Id)
  type[&R<:Tree] replaceType, // the type of replaced subterms (e.g. #Expr)
  &T t, // the top term 
  &R x, // the variable to be replaced
  &R sub, // the replacement term
  Refs(&T, Scope, Lookup) resolve // name resolution function
) {
  //assert isVar(varType, x): "x parameter must be a variable"; 

  round += 1; // start a new round of substitution
  
  // resolve the term, so that substRec knows 
  // the scope of binders to guide the substitution.
  Refs refs = justResolve(termType, t, resolve);
  
  assert validRefs(refs): "invalid reference graph";

  // do the actual recursive substitution
  &T newT = typeCast(termType, substRec(t, x, sub, refs, round));
  
  // resolve again, this time detecting capture and constructing renaming.
  map[loc, Tree] renaming = namePatch(termType, varType, newT, resolve);
  
  // ...and rename
  return rename(termType, newT, renaming);

}


@doc{Mark all terms in `t` to be from this substitution round.} 
private Tree replace(Tree t, int round) {
  t = visit (t) {
    case Tree tz => tz[@\loc = tz@\loc[fragment = "<round>"]]
      when tz@\loc? 
  }
  return t;  
}

/* this all doesn't work because &T matches everything
bool isVar(type[&T<:Tree] varType, Tree t) = true
  when
    &T _ := t;

bool isVar(type[&T<:Tree] varType, appl(_, [Tree arg])) = isVar(varType, arg);

default bool isVar(type[&T<:Tree] varType, _) = false;

&T getVar(type[&T<:Tree] varType, Tree t) = x
  when &T x := t;
  
default &T getVar(type[&T<:Tree] varType, appl(Production _, [Tree arg])) = getVar(varType, arg);
*/


private bool equalVar(Tree x, Tree y) = "<x>" == "<y>";

@doc{Recursively traverse a term, and apply substitutions throughout,
except when a term is a scope that bindgs `var`.}
private Tree substRec(Tree subj, Tree var, Tree exp, Refs refs, int round) {

  // if subject is scope of a binder of var; don't continue.
  // TODO: matching directly fails because var is an Expr, and
  // the thing in refs is an Id. The string comparision thus
  // performs equality modulo injections...

  if (subj@\loc?, <loc def, Tree x, loc scope, def> <- refs, 
      scope == subj@\loc, equalVar(var, x)) {
    return subj;
  } 
  
  // if subject is the variable, replace it.
  if (subj == var) {
    return replace(exp, round);
  }

  // recursive case
  if (appl(Production p, list[Tree] args) := subj) {
    Tree t2 = appl(p, [ substRec(a, var, exp, refs, round) | Tree a <- args ]);
    return subj@\loc? ? t2[@\loc=subj@\loc] : t2;
  }
  
  // otherwise, return unchanged.
  return subj;
}

@doc{Use myResolve to obtain a reference graph (Refs).}
Refs justResolve(type[&T<:Tree] typ, &T t, Refs(&T, Scope, Lookup) myResolve) {
  rel[loc, loc] lu(Tree name, loc use, Scope sc) {
    if (Env env <- sc, <_, _, name> <- env) {
      // if env defines name, return all defs in this env.
      return { <scope, def> | <loc scope, loc def, name> <- env };
    }
    return {};
  }
  return myResolve(t, [], lu);
}


@doc{Check properties on reference graphs (`Refs`):
  1. for every use referencing a decl, a self-referencing decl
     tuple exists with the same name and same scope.
  2. every decl is referencing itself (implied by 1 if use=decl)
}
bool validRefs(Refs refs) {
  usesWithBadNameOrScope = { <use, x, scope, decl> | 
    <loc use, Tree x, loc scope, loc decl> <- refs, <decl, x, scope, decl> notin refs }; 
  
  if (usesWithBadNameOrScope != {}) {
    println("WARNING: found bindings without well-formed target decls");
    for (<loc use, Tree x, loc scope, loc decl> <- usesWithBadNameOrScope) {
      println("use of <x> at <use>, referring <decl> in scope <scope>");
    }
  }
  
  return usesWithBadNameOrScope == {};
}

@doc{Compute set of free variables according to provided resolve function.}
set[&V] freeVars(type[&T<:Tree] termType, type[&V<:Tree] varType, &T t, Refs(&T, Scope, Lookup) resolve) {
  fv = {};
  
  rel[loc, loc] lu(Tree name, loc use, Scope sc) {
    if (Env env <- sc, <_, loc def, name> <- env, !isCapture(use, def)) {
      return {}; // we found a definition, so *not* free.
    }
    fv += { v | &V v := name };
    return {};
  } 
    
  resolve(t, [], lu);
  
  return fv;
}

@doc{Derive a new name from `x`, by (unsafely) appending suffix.
NB: this breaks matching on parsed terms with suffixes.}
&T prime(type[&T<:Tree] varType, &T x, str suffix = "_") 
  = y
  when 
    appl(Production p, list[Tree] args) := x,
    &T y := appl(p, args + [char(i) | int i <- chars(suffix) ]);

//TODO: this doesn't work because of the reified type/parsing bug
// but then it would be syntax safe.
//&T prime(type[&T<:Tree] varType, &T x) = parse(varType, "<x>_");
  
@doc{Obtain a fresh name relative to the set `names`.}
&T fresh(type[&T<:Tree] varType, &T x, set[&T] names) {
  int i = 0;
  while (x in names) {
    x = prime(varType, x, suffix = "<i>");
    i += 1;
  }
  return x;
}

@doc{Rename subtree representing variables according to `renaming`}
&T rename(type[&T<:Tree] typ, &T term, map[loc, Tree] renaming) {
  return visit (term) {
    case Tree t => renaming[t@\loc]
      when t@\loc?, t@\loc in renaming
  };
}


@doc{Obtain a rename map by resolving a term and detecting capture.}
map[loc, Tree] namePatch(type[&T<:Tree] typ, type[&V<:Tree] varType, &T t, Refs(&T, Scope, Lookup) resolve) {

   Resolver resolver = newResolver();
   Refs refs = resolve(t, [], resolver.lookup);
   
   assert validRefs(refs): "invalid reference graph";

   return capturesToRenaming(varType, resolver.captures(), refs);
}

@doc{Convert a set of captured declaration sites into a renaming map
that renames both declarations and usesto fresh names.}
map[loc, Tree] capturesToRenaming(type[&V<:Tree] varType, map[loc, Tree] captures, Refs refs) {
  set[Tree] allNames = refs.name; // NB: allnames does not include free vars 
  map[loc, Tree] ren = ();
  
  for (loc d <- captures) {
    Tree n = fresh(varType, captures[d], allNames);
    allNames += {n};
    ren[d] = n;
    ren += ( u: n | <loc u, _, _, d> <- refs ); 
  }

  return ren;
}

@doc{Construct a resolver object containing a lookup function
that detects name capture, and maintains a set name occurrences
that need to be renamed to avoid capture in the result.}
private Resolver newResolver() {
  map[loc, Tree] captures = ();
  
  rel[loc, loc] lookup(Tree name, loc use, Scope sc) {
    for (Env env <- sc, <loc scope, loc def, name> <- env) {
      if (!isCapture(use, def)) { 
        // TODO: return all non-capturing defs in single scope (?)
        return {<scope, def>};
      }
      // captures are renamed until a non-capturing decl is found
      captures[def] = name;
    }
    // not found
    return {};
  }
  
  return <lookup, map[loc,Tree]() { return captures; }>;
}

