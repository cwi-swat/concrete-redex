module paper::Credex

import ParseTree;
import String;
import List;
import IO;
import Type;


/*
 * Applying reduction relations
 */

alias R = set[Tree]; // reducts
alias CR = rel[Tree context, Tree redex]; // context reduce pairs
alias T = lrel[Tree from, Tree to]; // traces

R reduce(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C,Tree) red, &T t, set[str] rules)
  = { typeCast(#Tree, plug(tt, ctx2, rt)) |  <ctx1, rx> <- split(ct, t), //bprintln(ctx1), bprintln(rx), 
     str r <- rules,  <ctx2, rt> <- red(r, ctx1, rx) };

T trace(R(&T<:Tree) step, &T t0) {
  T trace = [];
  set[Tree] todo = {t0};
  solve (trace) {
    set[Tree] newTodo = {};
    for (&T t1 <- todo) {
      R next = step(t1);
      trace += [ <t1, t2> | t2 <- next ];
      newTodo += next;
    }
    todo = newTodo;
  }
  return trace;
}


/*
 * Split and plug
 */

rel[Tree,Tree] split(type[&T<:Tree] ctxType, Tree t) {
  ctx = parse(ctxType, "<t>", allowAmbiguity=true);
  
  rel[Tree, Tree] result = {};
  flattenAmbs(ctx, (Tree alt, Tree redex) {
    result += {<alt, redex>};
  });
  return result;
}

&T plug(type[&T<:Tree] tt, Tree ctx, Tree reduct) {
  Tree t = visit (ctx) {
    case Tree h => reduct when h is hole
  };
  return parse(tt, "<t>");
}

private Tree makeHole(Symbol sym) 
  = appl(prod(label("hole", sym),[lit("☐")],{}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])]);
 
private void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (t is hole) {
    k(makeHole(t.prod.def), t.args[0]); // skip over "hole" injection
    return;
  }
  
  switch (t) {
    case appl(Production p, list[Tree] args): {
      for (int i <- [0..size(args)]) {
        flattenAmbs(args[i], (Tree ctx, Tree redex) {
          k(appl(p, args[0..i] + [ctx] + args[i+1..]), redex); 
        });
      }
    }
    
    case amb(set[Tree] alts): {
      for (Tree a <- alts) {
        flattenAmbs(a, (Tree ctx, Tree redex) {
          k(ctx, redex);
        });
      } 
    }
  }
  
}


/*
 * Generic, capture-avoiding substitution
 */

alias Env = rel[loc scope, loc decl, Tree name];
alias Lookup = rel[loc scope, loc decl](Tree, loc, list[Env]);
alias Refs = rel[loc use, Tree name, loc scope, loc decl];
alias Resolver[&T] = Refs(&T, list[Env], Lookup); 

 
private int round = -1;

&T subst(type[&T<:Tree] tt, Tree x, Tree r, &T t, Resolver[&T] resolve) {
  round += 1;
  new = subst(x, r, t, resolve(t, [], defaultLookup));
  return typeCast(tt, rename(new, nameFix(new, resolve)));
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

private Tree mark(Tree t, int round) {
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
    case Tree x => ren[x@\loc] when x@\loc?, x@\loc in ren
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
  int i = 0;
  while (x in names) {
    x = appl(x.prod, x.args + [char(c) | int c <- chars("<i>") ])[@\loc=x@\loc];
    i += 1;
  }
  return x;
}

