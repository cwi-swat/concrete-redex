module credex::Matching

import Type;
import List;
import ParseTree;
import Node;

/*
 * TODO:
 * - many sorted contexts: requires different param to `make`
 * - remove payload function
 * - support hybrid terms (so not just Tree, but also ADTs with maps etc.)
 */

@doc{Match a tree according to the data type ctx and produce all matches}
list[&C] toCtx(type[&C<:node] ctx, Tree t) {
  cs = [];
  
  toCtx(ctx, ctx.definitions[ctx.symbol], t, void(node n) {
    cs += [typeCast(ctx, n)];
  });
  
  return cs;
}

@doc{Convert a list of tree arguments to list of context arguments based on a list of symbols}
void toCtx(type[&C<:node] ctx, list[Symbol] syms, list[Tree] args, void(list[value]) k) {
  if (syms == []) {
    if (args == []) {
      k([]);
    }
    return;
  }

  toCtx(ctx, syms[0], args, void(list[value] ns1) {

     // TODO: pass a delta int into the continuation to avoid this function.
     // this also does not work for nested lists..
     int payload(list[value] xs) = ( 0 | it + payload(x) | value x <- xs );
     default int payload(value x) = 1;
     
     toCtx(ctx, syms[1..], args[payload(ns1)..], void(list[value] ns2) {
        k(ns1 + ns2);
     });
  });
}


@doc{Convert a list of tree arguments to list of context arguments based on symbol}
void toCtx(type[&C<:node] ctx, \list(Symbol elt), list[Tree] args, void(list[value]) k) {
  //println("list elem");
  int i = 0;
  list[value] ns = [];

  k([ns]); // empty; TODO: turn into 1 do-while loop.
  while (i < size(args), match(elt, args[i])) {
   ns += [uninject(elt, args[i])];
   i += 1;
   k([ns]);
  }
}


void toCtx(type[&C<:node] ctx, s:adt(_, _), list[Tree] args, void(list[value]) k) {
 if (args == []) {
   return;
 }
 toCtx(ctx, ctx.definitions[s], args[0], void(node n) {
   k([n]);
 });
} 
 

void toCtx(type[&C<:node] ctx, label(_,  Symbol s), list[Tree] args, void(list[value]) k) 
  = toCtx(ctx, s, args, k);

default void toCtx(type[&C<:node] ctx, Symbol s, list[Tree] args, void(list[value]) k) {
  if (args == []) {
    return;
  }
  if (match(s, args[0])) {
    k([uninject(s, args[0])]);
  }
}

@doc{Converting a tree to a context based on production}
void toCtx(type[&C<:node] ctx, cons(label(str name, _), list[Symbol] syms, _, _), Tree t, void(node) k) {
  if (name == "hole") {
    // is this a special case of the below one?
    k(make(ctx, name, [t]));
  }
  else if (label(name, _) := t.prod.def) {
    toCtx(ctx, syms, astArgs(t), void(list[value] args) {
      k(make(ctx, name, args));
    }); 
  }
}

void toCtx(type[&C<:node] ctx, choice(_, set[Production] alts), Tree t, void(node) k) {
  for (Production a <- alts) {
    toCtx(ctx, a, t, k);
  } 
}

@doc{Convert a context value to string}
str ctx2str(value ctx) {
  switch (ctx) {
    case Tree t: return "<t>";
    case list[value] l: return "[<intercalate(", ", [ ctx2str(x) | value x <- l ])>]";
    case node n: return "<getName(n)>(<intercalate(", ", [ ctx2str(x) | value x <- getChildren(n) ])>)";
    default: return "<ctx>";
  }
}  

@doc{Match modulo injections}  
bool match(Symbol s, appl(prod(label(_, s2), list[Symbol] syms, set[Attr] attrs), list[Tree] args))
  = match(s, appl(prod(s2, syms, attrs), args));
  
bool match(Symbol s, appl(prod(s, _, _), _)) = true;

bool match(Symbol s, appl(prod(_, [Symbol s2], _), [Tree arg])) = match(s, arg);

default bool match(Symbol _, Tree _) = false;

@doc{Remove unneeded injections around a matched tree}
Tree uninject(Symbol s, t:appl(prod(s, _, _), _)) = t;

Tree uninject(Symbol s, t:appl(prod(label(_, s), _, _), _)) = t;

Tree uninject(Symbol s, appl(prod(_, [Symbol _], _), [Tree arg])) = uninject(s, arg);

default Tree uninject(Symbol _, Tree t) = t;


@doc{Flatten regulars in a list of trees into one list}
list[Tree] flatten(list[Tree] args) = ( [] | it + flatten(a) | Tree a <- args );

list[Tree] flatten(appl(regular(_), list[Tree] args)) = flatten(args);

default list[Tree] flatten(Tree t) = [t];

@doc{Filter out keywords, layout etc. and flatten arguments of t}
list[Tree] astArgs(Tree t) = [ a | Tree a <- flatten(t.args), isAst(a.prod.def) ];

@doc{Determine if a symbol represents AST content}  
bool isAst(cilit(_)) = false;

bool isAst(lit(_)) = false;

bool isAst(layouts(_)) = false;

default bool isAst(Symbol _) = true;

