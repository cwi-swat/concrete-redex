module lang::credex::Resolve

import ParseTree;
import String;
import IO;

alias Env = rel[loc scope, loc decl, Tree name];
alias Lookup = rel[loc scope, loc decl](Tree, loc, list[Env]);
alias Refs = rel[loc use, Tree name, loc scope, loc decl];

alias Resolver = tuple[
  void(Tree) declare,
  void(Tree) refer,
  void(Tree, void()) scope,
  void(Tree) resolve,
  void(Tree) resolveKids,
  Refs() refs
];

int getMark(loc l) = l.fragment != "" ? toInt(l.fragment) : -1;
loc mark(loc l, int x) = l[fragment="<x>"]; 


rel[loc, loc] defaultLookup(Tree x, loc u, list[Env] envs) {
  for (Env env <- envs) {
    decls = {<s, d> | <s, d, x> <- env };
    if (decls != {}) return decls;
  }
  return {}; // not found
}
  
// for now, single sorted...
Resolver makeResolver(type[&T<:Tree] tt, void(&T, Resolver) myResolve, Lookup lookup = defaultLookup) {
  list[loc] scopes = [];
  Refs refs = {};
  list[Env] envs = [];
  
  int theMark = -1;
  
  Resolver this;
  
  loc mark(loc l) = theMark >= 0 ? mark(l, theMark) : l;
  
  void scope(Tree t, void() block) {
    scopes += [t@\loc];
    envs = [{}] + envs;
    block();
    scopes = scopes[..-1];
    envs = envs[1..];
  }
  
  void declare(Tree t) {
    refs += {<mark(t@\loc), t, scopes[-1], mark(t@\loc)>}; // self ref
    envs[0] += {<scopes[-1], mark(t@\loc), t>};
  }
  
  void refer(Tree t) {
    refs += {<mark(t@\loc), t, s, d> | <loc s, loc d> <- lookup(t, mark(t@\loc), envs) };
  }
  
  
  void withMark(Tree t, void() block) {
    marked = t@\loc? && getMark(t@\loc) >= 0;
    if (marked) {
      theMark = getMark(t@\loc);
    }
    block();
    if (marked) {
      theMark = -1;
    }
  }
  
  void resolveKids(Tree t) {
    withMark(t, () {
      if (appl(Production p, list[Tree] args) := t) {
        for (int i <- [0..size(args)], i mod 2 == 0) {
          resolve(args[i]);
        }
      }
    }); 
  }
  
  void resolve(Tree t) {
    if (&T typed := t) {
      withMark(t, () { myResolve(typed, this); });
    }
    else {
      resolveKids(t);
    }
  }
  
  this = <declare, refer, scope, resolve, resolveKids, Refs() { return refs; }>;
  return this;
  
}