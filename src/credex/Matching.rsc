module credex::Matching

import Type;
import List;
import ParseTree;
import Node;
import IO;

/*
 * TODO:
 * - remove payload function
 * - support hybrid terms (so not just Tree, but also ADTs with maps etc.)
 * - fix uninject for lexicals... (classcast exception)
 * - store problem in plug
 * - not possible to put contexts into terms (e.g. for callcc).
 */

/*

Make simplifying assumption: hole is always in a Tree
so do simul traversal, updating values in conf from context
when hit tree, do the loc trick.

*/

@doc{Plug the reduct back into original term where the context's hole is located.}
&T plug(type[&T<:Tree] typ, node ctx, &T term, Tree reduct) {
  // traverse ctx and term in simultaneously, until hole(), then put in reduct.
  // for now it's doing two traversals, for simplicity's sake.
  // this is wrong! We lose changes in the context, even it contains
  // a concrete store for instance; hence we need simul traversal.
  // which is rather complicated because of injections, astArgs and flattening.
  // Q: do we need to have stores etc. be part of the term?
  // it could still be an extra param in the reduction relation,
  // but then you have to declare it everywhere, even if you don't access it.
  // so we need adts as configurations + ordinary values.
  /*
  can we use keyword params? But what about the result type?
  
  CR rule("lookup", (AExp)`<Id x>`))
  = <s, (AExp)`<Int i>`>
  when 
    isDefined(x, s), 
    Int i := lookup(x, s); 


  CR rule("add", (AExp)`<Int i1> + <Int i2>`) =  (AExp)`<Int i>` 
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 + n2>";
  
  
  */
  holeLocs = [ l | /"hole"(loc l) := ctx ];
  assert size(holeLocs) == 1: "multiple holes in context";

  return visit (term) {
    case Tree t => reduct when t@\loc?, t@\loc == holeLocs[0]
  }
}

alias TypeMap = map[Symbol, type[value]];

@doc{Match a tree according to the data type ctx and produce all matches.
The extra reified types are needed to construct correct context values
when there is more than one context ADT (e.g. many-sorted contexts).}
rel[&C, Tree] split(type[&C<:node] ctx, Tree t, type[node] ctxes...) {
  typeMap = ( typ.symbol: typ | typ <- ctxes + [ctx] );
  
  cs = {};
  toCtx(typeMap, ctx.definitions[ctx.symbol], t, void(node n, list[Tree] redex) {
    //println("Succes: <ctx2str(n)>");
    assert size(redex) == 1: "multiple redexes";
    cs += {<typeCast(ctx, n), redex[0]>};
  });
  
  return cs;
}

@doc{Convert a list of tree arguments to list of context arguments based on a list of symbols}
void toCtx(TypeMap tm, list[Symbol] syms, list[Tree] args, void(list[value], list[Tree]) k) {
  if (syms == []) {
    if (args == []) {
      k([], []);
    }
    return;
  }

  // TODO: pass a delta int into the continuation to avoid this function.
  // this also accidentally flattens nested lists..
  int payload(list[value] xs) = ( 0 | it + payload(x) | value x <- xs );
  default int payload(value x) = 1;

  toCtx(tm, syms[0], args, void(list[value] ns1, list[Tree] r1) {
     //println("matched <syms[0]> -\> <ctx2str(ns1)>");
     toCtx(tm, syms[1..], args[payload(ns1)..], void(list[value] ns2, list[Tree] r2) {
        //println("matched <syms[1..]> -\> <ctx2str(ns2)>");
        k(ns1 + ns2, r1 + r2);
     });
  });
}


@doc{Convert a list of tree arguments to list of context arguments based on symbol}
void toCtx(TypeMap tm, \list(Symbol elt), list[Tree] args, void(list[value], list[Tree]) k) {
  //println("list elem");
  int i = 0;
  list[value] ns = [];

  k([ns], []); // empty; TODO: turn into 1 do-while loop.
  while (i < size(args), match(elt, args[i])) {
    ns += [uninject(elt, args[i])];
    i += 1;
    k([ns], []); // NB: we don't allow lists of contexts, so [] as redexes is ok.
  }
}

// TODO: change list[Tree] -> list[value]
// add cases for other type constructors (map,list,set) etc.
void toCtx(TypeMap tm, s:adt(_, _), list[Tree] args, void(list[value], list[Tree]) k) {
 if (args == []) {
   return;
 }
 //println("trying prods of <s>");
 toCtx(tm, tm[s].definitions[s], args[0], void(node n, list[Tree] redex) {
   k([n], redex);
 });
} 
 

void toCtx(TypeMap tm, label(_,  Symbol s), list[Tree] args, void(list[value], list[Tree]) k) 
  = toCtx(tm, s, args, k);

default void toCtx(TypeMap tm, Symbol s, list[Tree] args, void(list[value], list[Tree]) k) {
  //println("trying symbol <s>");
  if (args == []) {
    return;
  }
  if (match(s, args[0])) {
    k([uninject(s, args[0])], []);
  }
  //else {
  //  println("****** failed to match \'<args[0]>\' (<args[0].prod>) to <s>");
  //}
}

@doc{Converting a tree to a context based on production}
void toCtx(TypeMap tm, cons(label(str name, Symbol ctxSym), list[Symbol] syms, _, _), Tree t, void(node, list[Tree]) k) {
  // here we need another case distinction: if t is not a tree, but a node
  // then, do not do astArgs etc.
  if (name == "hole") {
    //println("Found hole: <ctxSym>");
    k(make(tm[ctxSym], "hole", [t@\loc? ? t@\loc : |tmp:///dummy|]), [t]);
  }
  else if (label(name, _) := t.prod.def) {
    //println("trying prod <t.prod>");
    toCtx(tm, syms, astArgs(t), void(list[value] args, list[Tree] redex) {
      k(make(tm[ctxSym], name, args), redex);
    }); 
  }
}

void toCtx(TypeMap tm, choice(_, set[Production] alts), Tree t, void(node, list[Tree]) k) {
  for (Production a <- alts) {
    toCtx(tm, a, t, k);
  } 
}

@doc{Convert a context value to string}
str ctx2str(value ctx, bool printLoc = false) {
  switch (ctx) {
    case "hole"(loc l): return printLoc ? "[<l>]" : "☐";
    case Tree t: return "<t>";
    case list[value] l: return "[<intercalate(", ", [ ctx2str(x, printLoc=printLoc) | value x <- l ])>]";
    case node n: return "<getName(n)>(<intercalate(", ", [ ctx2str(x, printLoc=printLoc) | value x <- getChildren(n) ])>)";
    default: return "<ctx>";
  }
}  

@doc{Match modulo injections}  
bool match(Symbol s, appl(prod(label(_, s2), list[Symbol] syms, set[Attr] attrs), list[Tree] args))
  = match(s, appl(prod(s2, syms, attrs), args));
  
bool match(Symbol s, appl(prod(s, _, _), _)) = true;

bool match(sort(str name), appl(prod(lex(name), _, _), _)) = true;

bool match(Symbol s, appl(prod(_, [Symbol s2], _), [Tree arg])) = match(s, arg);

default bool match(Symbol _, Tree _) = false;

@doc{Remove unneeded injections around a matched tree}
Tree uninject(Symbol s, t:appl(prod(s, _, _), _)) = t;

Tree uninject(Symbol s, t:appl(prod(label(_, s), _, _), _)) = t;

Tree uninject(Symbol s, appl(prod(_, [Symbol _], _), [Tree arg])) = uninject(s, arg);

// TODO: rename
//Tree uninject(sort(str name), t:appl(prod(lex(name), _, _), _))
//  = appl(prod(sort(name), [lex(name)], {}), t)[@\loc=t@\loc];
// throws a classcast exception. 

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

