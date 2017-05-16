module paper::MatchRedex

import ParseTree;
import Node;
import Type;
import IO;
import List;
import String;

extend paper::TraceRedex;

alias CR = rel[node context, Tree reduct];

R reduce(type[&C<:node] ct, CR(str,&C) red, &T<:Tree t, set[str] rules, type[node] cts...)
  = { plug(ctx2, rt, t) |  ctx1 <- split(ct, t, cts),
        str r <- rules, <ctx2, rt> <- red(r, ctx1) };

        
node plugCtx(node ctx1, node ctx2) {
  loc origin(node n) = typeCast(#loc, getKeywordParameters(n)["src"]);
    
  return top-down-break visit (ctx1) {
    case Tree _: ; // there can be no contexts below a Tree
    case node n => ctx2
      when origin(n) == origin(ctx2)
  }
}
        
        
/*
 * TODO:
 * - remove payload function
 * - support hybrid terms (so not just Tree, but also ADTs with maps etc.)
 * - fix uninject for lexicals... (classcast exception)
 * - not possible to put contexts into terms (e.g. for callcc).
 */

private Tree getArg(int i, Tree t) = astArgs(t)[i]; // for now.


// this can be made much more efficient if we apply
// a kind of lazy iterator/zipper pattern.
private list[Tree] updateArg(int i, Tree arg, list[Tree] args) {
  //println("************** UPDATING <arg> of type <arg.prod>");
  j = 0;
  jAst = 0;
  bool updated = false;
  for (Tree t <- args) {
    //println("i = <i>, j = <j>, jAst = <jAst>");
    //println("Updating <t>?");
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
          //println("Found it: args[j].args[k] = \"<args[j].args[k]>\" becomes \"<arg>\"");
          updated = true;
          //println("OLDARGS = <intercalate(", ", [ "<na>" | na <- args ])>   ");
              
          //println("BEFORE Args[<j>].args[<k>] = <args[j].args[k]>");
          cur = args[j];
          args = args[0..j] + [appl(cur.prod, cur.args[0..k] + [arg] + cur.args[k+1..])[@\loc=cur@\loc]] + args[j+1..];
          //println("AFTER: Args[<j>].args[<k>] = <args[j].args[k]>");
          //println("OLDARGS = <intercalate(", ", [ "<na>" | na <- args ])>   ");
          return args;
        }
        jAst += 1;
        k += 1;
      }
      continue;
    }
      
    if (jAst == i) {
      //println("Found it outside of list: args[j] = \"<args[j]>\" becomes \"<arg>\"");
      updated = true;
      
      return args[0..j] + [arg] + args[j+1..];
    }
    
    jAst += 1;
    j += 1;
      
  }
  if (!updated) {
    throw "error";
  }
  return args; 
}

@doc{Plug the reduct back into original term where the context's hole is located. 
Meanwhile, create a new concrete syntax tree based on the last argument (the original term).}
Tree plug(node n, Tree reduct, x:appl(Production p, list[Tree] args)) {
  //println("PLUG: <ctx2str(n)>");
  //println("REDUCT: <reduct>");

  if (n is hole) {
    //println("Returning reduct...");
    return reduct;
  }  

  i = 0;
  newArgs = args;
  
  
  for (value v <- getChildren(n)) {
    //println("Current kid: <ctx2str(v)>");
    //println("i  = <i>");
    
    if (i >= size(astArgs(x))) {
      assert v == [];
      assert i == size(getChildren(n)) - 1;
      break; 
    }
    
    //println("Current arg: <getArg(i, x)>");

    
    switch (v) {

      case list[Tree] l: {
        for (Tree t <- l) {
          //println("CURRENT list elt: <t>");
          //println("List elt prod: <t.prod>");
          //println("Current arg prod: <getArg(i, x).prod>");
          //if (match(t.prod.def, getArg(i, x))) {
            //println("Matched!");
            t2 = reinject(getArg(i, x).prod, t);
            //println("GetArg = <getArg(i, x)>");
            //println("TTTTTTT 2 = <t2>");
            if (t2 != getArg(i, x)) {
              //println("Updated new args from list !!!");
              newArgs = updateArg(i, t2, newArgs);
              //println("NEWARGS = <intercalate(", ", [ "<na>" | na <- newArgs ])>   ");
              //for (bla <- newArgs) {
              //  //println("New arg --\> |<bla>|");
              //}
            } 
          //}
          i += 1;
        }
        continue; // don't i+=1 twice...
      }
        // we never have list of contexts, so the hole is not here.
        // so no recursion needed, but we need to check if anything has changed and
        // take it from l, not args
        
      case Tree t:  
         if (match(t.prod.def, getArg(i, x))) {
           t2 = reinject(getArg(i, x).prod, t);
           //println("In context: <t.prod>");
           //println("In term: <getArg(i, x).prod>");
           //println("Reinjected: <t2.prod>");
           if (t2 != getArg(i, x)) {
             //println("Updated new args!!! case tree");
             newArgs = updateArg(i, t2, newArgs);
             //println("case tree NEWARGS = <intercalate(", ", [ "<na>" | na <- newArgs ])>   ");
           } 
         }
         
      case node k: { 
        // here basically we have to find the position in args
        // where to continue plugging. We can use the src loc for this?
        newArgs = updateArg(i, plug(k, reduct, getArg(i, x)), newArgs);
        //println("Updated new args!!!");
        //println("case node NEWARGS = <intercalate(", ", [ "<na>" | na <- newArgs ])>   ");
      }
    }
    
    i += 1;
  }
  
  //println("ctx: <ctx2str(n)>");
  //for (Tree z <- newArgs) {
  //  //println("==================\> <z> (<z.prod>)");
  //}
  
  return appl(p, newArgs)[@\loc=x@\loc];
  
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
    ////println("Succes: <ctx2str(n)>");
    assert size(redex) == 1: "multiple redexes";
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
     ////println("matched <syms[0]> -\> <ctx2str(ns1)>");
     toCtx(tm, syms[1..], args[payload(ns1)..], void(list[value] ns2, list[Tree] r2) {
        ////println("matched <syms[1..]> -\> <ctx2str(ns2)>");
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
  ////println("trying symbol <s>");
  if (args == []) {
    return;
  }
  if (match(s, args[0])) {
    k([uninject(s, args[0])], []);
  }
  //else {
  //  //println("****** failed to match \'<args[0]>\' (<args[0].prod>) to <s>");
  //}
}

@doc{Converting a tree to a context based on production}
void toCtx(TypeMap tm, cons(label(str name, Symbol ctxSym), list[Symbol] syms, _, _), Tree t, void(node, list[Tree]) k) {
  // here we need another case distinction: if t is not a tree, but a node
  // then, do not do astArgs etc.
  ////println("In cons: <name> of <ctxSym>");
  ////println("prod = <t.prod>");
  if (name == "hole") {
    ////println("Found hole: <ctxSym>");
    ////println("T = <t> (<t.prod.def>)");
    k(make(tm[ctxSym], "hole", [t], ("src": t@\loc)), [t]);
  }
  else if (name == "inject") {
    ////println("Injecting another context");
    toCtx(tm, [syms[0]], [t], void(list[value] args, list[Tree] redex) {
      k(make(tm[ctxSym], name, args, ("src": t@\loc)), redex);
    });
  }
  else if (label(name, _) := t.prod.def) {
    ////println("trying prod <t.prod>");
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

        