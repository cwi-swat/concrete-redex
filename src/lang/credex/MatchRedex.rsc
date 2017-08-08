module paper::MatchRedex

import ParseTree;
import Node;
import Type;
import IO;
import List;
import String;

/*
 * IMPORTANT: This is very experimental code an not maintained; use at your own risk.
 */ 


extend paper::TraceRedex;

alias CR = rel[node context, Tree reduct];

RR apply(type[&C<:node] ct, CR(str,&C) red, &T<:Tree t, set[str] rules, type[node] cts...)
  = { <r, plug(ctx2, rt, t)> |  ctx1 <- split(ct, t, cts),
    bprintln("CTX <ctx2str(ctx1)>"),
        str r <- rules, <ctx2, rt> <- red(r, ctx1)
        , bprintln(" === <r> ===\> <rt>")
         };

R reduce(type[&C<:node] ct, CR(str,&C) red, &T<:Tree t, set[str] rules, type[node] cts...)
  = { plug(ctx2, rt, t) |  ctx1 <- split(ct, t, cts),
        str r <- rules, <ctx2, rt> <- red(r, ctx1) };

        
node plugCtx(node ctx1, node ctx2) {
  loc origin(node n) = typeCast(#loc, getKeywordParameters(n)["src"]);
    
  return top-down-break visit (ctx1) {
    case Tree _: ; // there can be no contexts below a Tree
    case node n => ctx2 when origin(n) == origin(ctx2)
  }
}
        
        
/*
 * TODO:
 * - remove payload function
 * - remove redex passing.
 * - support hybrid terms (so not just Tree, but also ADTs with maps etc.)
 * - fix uninject for lexicals... (classcast exception)
 * - not possible to put contexts into terms (e.g. for callcc).
 */

alias Cursor = tuple[Tree get, list[Tree](Tree) update];

// this is very tricky code... basically a flattening, non-ast skipping, iterator
Cursor findArg(int i, list[Tree] args) {
  j = 0;
  jAst = 0;

  for (Tree t <- args) {
    if (!isAst(t.prod.def)) {
      j += 1;
      continue;
    }
    
    if (t.prod is regular) {
      subArgs = t.args;
      k = 0;
      for (Tree tSub <- subArgs) {
        if (!isAst(tSub.prod.def)) {
          k += 1;
          continue;
        }
        if (jAst == i) {
          return <args[j].args[k], 
             list[Tree](Tree arg) {
               cur = args[j];
               return args[0..j] + [appl(cur.prod, cur.args[0..k] + [arg] + cur.args[k+1..])[@\loc=cur@\loc]] + args[j+1..];
             }>;
        }
        jAst += 1;
        k += 1;
      }
      continue;
    }
      
    if (jAst == i) {
      return <args[j], list[Tree](Tree arg) { return args[0..j] + [arg] + args[j+1..]; }>;
    }
    
    jAst += 1;
    j += 1;
      
  }
  
  assert false: "argument <i> not found";  
}


@doc{Plug the reduct back into original term where the context's hole is located. 
Meanwhile, create a new concrete syntax tree based on the last argument (the original term).}
Tree plug(node n, Tree reduct, x:appl(Production p, list[Tree] args)) {

  if (n is hole) {
    return reduct;
  }  

  @doc{Update the syntax tree at `cursor` if `t` is not the same}
  void update(Cursor cursor, Tree t) {
    if (match(t.prod.def, cursor.get)) {
      t2 = reinject(cursor.get.prod, t);
      if (t2 != cursor.get) {
        args = cursor.update(t2);
      } 
    }
  }
  
  int arity = size(astArgs(x));

  i = 0;
    
  for (value v <- getChildren(n)) {
    
    if (i >= arity) {
      println("X = <x>");
      println("ctx = <ctx2str(n)>");
      println("V = <ctx2str(v)>");
      assert v == [];
      i += 1;
      continue;
    }

    switch (v) {

      case list[Tree] l: 
        for (Tree t <- l) {
          cursor = findArg(i, args);
          update(cursor, t);
          i += 1; 
        }
        
      case Tree t: {
        cursor = findArg(i, args);
        update(cursor, t);
        i += 1;
      }  
         
      case node k: { 
        cursor = findArg(i, args);
        args = cursor.update(plug(k, reduct, cursor.get));
        i += 1;
      }
    }
    
  }
  
  return appl(p, args)[@\loc=x@\loc];
  
}
alias TypeMap = map[Symbol, type[value]];

@doc{Match a tree according to the data type ctx and produce all matches.
The extra reified types are needed to construct correct context values
when there is more than one context ADT (e.g. many-sorted contexts).}
set[&C] split(type[&C<:node] ctx, Tree t, list[type[node]] ctxes) {
  typeMap = ( typ.symbol: typ | typ <- ctxes + [ctx] );
  
  cs = {};
  // todo: remove redex passing; it's not needed anymore since we do
  // deep match in the reduction rules.
  toCtx(typeMap, ctx.definitions[ctx.symbol], t, void(node n, list[Tree] redex) {
    //println("Succes: <ctx2str(n)>");
    //println("SIZE: <size(redex)>");
    for (size(redex) > 1, rx <- redex) {
      println("REDEX: <redex>");
    }
    assert size(redex) == 1: "multiple or no redexes";
    
    cs += typeCast(ctx, n);
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
  ////println("list elem");
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
 ////println("trying prods of <s>");
 toCtx(tm, tm[s].definitions[s], args[0], void(node n, list[Tree] redex) {
   k([n], redex);
 });
} 
 

void toCtx(TypeMap tm, label(_,  Symbol s), list[Tree] args, void(list[value], list[Tree]) k) 
  = toCtx(tm, s, args, k);

default void toCtx(TypeMap tm, Symbol s, list[Tree] args, void(list[value], list[Tree]) k) {
  println("trying symbol <s>");
  if (args == []) {
    return;
  }
  if (match(s, args[0])) {
    k([uninject(s, args[0])], []);
  }
  else {
    println("****** failed to match \'<args[0]>\' (<args[0].prod>) to <s>");
  }
}

@doc{Converting a tree to a context based on production}
void toCtx(TypeMap tm, cons(label(str name, Symbol ctxSym), list[Symbol] syms, _, _), Tree t, void(node, list[Tree]) k) {
  // here we need another case distinction: if t is not a tree, but a node
  // then, do not do astArgs etc.
  ////println("In cons: <name> of <ctxSym>");
  ////println("prod = <t.prod>");
  //println("Syms[0] = <syms[0]>");
  //println("t = <t.prod.def>");
  //
  // todo: fix label issue here.
  if (name == "hole", label(_, Symbol s) := syms[0], match(s, t)) {
    //println("Found hole: <ctxSym>");
    //println("T = <t> (<t.prod.def>)");
    //"src": t@\loc
    k(make(tm[ctxSym], "hole", [t], ()), [t]);
  }
  else if (name == "inject") {
    //println("Injecting another context");
    toCtx(tm, [syms[0]], [t], void(list[value] args, list[Tree] redex) {
      k(make(tm[ctxSym], name, args, ("src": t@\loc)), redex);
    });
  }
  else if (label(name, _) := t.prod.def) {
    //println("trying prod <t.prod>");
    toCtx(tm, syms, astArgs(t), void(list[value] args, list[Tree] redex) {
      k(make(tm[ctxSym], name, args, ("src": t@\loc)), redex);
    }); 
  }
}

void toCtx(TypeMap tm, choice(_, set[Production] alts), Tree t, void(node, list[Tree]) k) {
  for (Production a <- alts) {
    //println("Trying alt: <a> against <t>");
    toCtx(tm, a, t, k);
  } 
}

@doc{Convert a context value to string}
str ctx2str(value ctx, bool printLoc = false) {
  switch (ctx) {
    //case "hole"(Tree t): return printLoc ? "[<l>]" : "☐";
    case Tree t: return "<t>";
    case list[value] l: return "[<intercalate(", ", [ ctx2str(x, printLoc=printLoc) | value x <- l ])>]";
    case node n: {
      args = intercalate(", ", [ ctx2str(x, printLoc=printLoc) | value x <- getChildren(n) ]);
      kws = getKeywordParameters(n);
      return "<getName(n)>(<args><"src" in kws ? ", src=<kws["src"]>" : "">)";
    }
    default: return "<ctx>";
  }
}  

@doc{Match modulo injections}  
bool match(Symbol s, appl(prod(label(_, s2), list[Symbol] syms, set[Attr] attrs), list[Tree] args))
  = match(s, appl(prod(s2, syms, attrs), args));
  
bool match(Symbol s, appl(prod(s, _, _), _)) = true;

bool match(sort(str name), appl(prod(lex(name), _, _), _)) = true;

bool match(Symbol s, appl(prod(_, [Symbol s2], _), [Tree arg])) = match(s, arg);

// Not sure here.
//bool match(\iter-star-seps(Symbol s, _), appl(prod(Symbol s, _, _), [Tree arg])) = true;

default bool match(Symbol _, Tree _) = false;

@doc{Add injections according to production}
Tree reinject(Production p, Tree t) = t
  when p.def == t.prod.def;

default Tree reinject(Production p, Tree t) 
  = appl(p, [t])[@\loc=t@\loc];



@doc{Remove unneeded injections around a matched tree}
Tree uninject(Symbol s, t:appl(prod(s, _, _), _)) = t;

Tree uninject(Symbol s, t:appl(prod(label(_, s), _, _), _)) = t;

default Tree uninject(Symbol s, appl(prod(_, [Symbol _], _), [Tree arg])) = uninject(s, arg);

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

        