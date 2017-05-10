module lang::lambda::Contexts

import lang::lambda::Lambda;
import ParseTree;
import Type;
import List;
import IO;
import Node;

data E
  = apply(list[Value] vals, E ctx, list[Expr] exprs)
  | if0(E ctx, Expr then, Expr els)
  | hole(Expr expr)
  ;
  
/*
(+ 1 2)

hole((+ 1 2))
apply([], +, [1, 2]);
apply([+], 1, [2]);
apply([+, 1], 2, []);

*/
  
str ctx2str(value ctx) {
  switch (ctx) {
    case Tree t: return "<t>";
    case list[value] l: return "[<intercalate(", ", [ ctx2str(x) | value x <- l ])>]";
    case node n: return "<getName(n)>(<intercalate(", ", [ ctx2str(x) | value x <- getChildren(n) ])>)";
    default: return "<ctx>";
  }
}  
  
//public java &T make(type[&T] typ, str name, list[value] args);

bool match(Symbol s, appl(prod(label(_, s2), list[Symbol] syms, set[Attr] attrs), list[Tree] args))
  = match(s, appl(prod(s2, syms, attrs), args));
  
bool match(Symbol s, appl(prod(s, _, _), _)) = true;

bool match(Symbol s, appl(prod(_, [Symbol s2], _), [Tree arg])) = match(s, arg);

default bool match(Symbol _, Tree _) = false;

list[Tree] flatten(list[Tree] args) = ( [] | it + flatten(a) | Tree a <- args );

// todo: don't flatten injections, but use match for that.
//list[Tree] flatten(appl(prod(_, [Symbol _], _), [Tree arg])) = [arg];

list[Tree] flatten(appl(regular(_), list[Tree] args)) = ( [] | it + flatten(arg) | Tree arg <- args );

default list[Tree] flatten(Tree t) = [t];

list[Tree] astArgs(Tree t)
  = [ a | Tree a <- flatten(t.args), isAst(a.prod.def) ];
  
bool isAst(cilit(_)) = false;
bool isAst(lit(_)) = false;
bool isAst(layouts(_)) = false;
default bool isAst(Symbol _) = true;

void toctx(type[&C<:node] ctx, list[Symbol] syms, list[Tree] args, void(list[value]) k) {
  if (syms == [], args != []) {
    println("no syms, but still args");
    return;
  }
  if (syms == [], args == []) {
    k([]);
    return;
  }
  println("Trying first sym <syms[0]>");
  toctx(ctx, syms[0], args, void(list[value] ns1) {
     println("HEAD: ");
     for (v <- ns1) {
       if (list[value] l := v) {
         println("   [<intercalate(", ", ["<x>" | value x <- l ])>]");
       }
       else {
         println("   <v> ");
       }
     }
     int payload(list[value] xs) = ( 0 | it + payload(x) | value x <- xs );
     default int payload(value x) = 1;
     
     toctx(ctx, syms[1..], args[payload(ns1)..], void(list[value] ns2) {
        println("TAIL: ");
        for (v <- ns2) {
          if (list[value] l := v) {
            println("   [<intercalate(", ", ["<x>" | value x <- l ])>]");
          }
          else {
            println("   <v> ");
          }
        }
        k(ns1 + ns2);
     });
  });
}

Tree uninject(Symbol s, t:appl(prod(s, _, _), _)) = t;
Tree uninject(Symbol s, t:appl(prod(label(_, s), _, _), _)) = t;
Tree uninject(Symbol s, appl(prod(_, [Symbol _], _), [Tree arg])) = uninject(s, arg);
default Tree uninject(Symbol _, Tree t) = t;

void toctx(type[&C<:node] ctx, \list(Symbol elt), list[Tree] args, void(list[value]) k) {
  println("list elem");
  int i = 0;
  list[value] ns = [];
  println("Trying empty");
  k([ns]); // empty;
  while (i < size(args), match(elt, args[i])) {
   ns += [uninject(elt, args[i])];
   i += 1;
   println("Trying list of length <i>");
   k([ns]);
  }
  if (i < size(args), !match(elt, args[i])) {
    println("MATCH FAIL:");
    println("Symbol: <elt>");
    println("Term: <args[i]>");
  }
  println("fail from list match");
}


void toctx(type[&C<:node] ctx, s:adt(_, _), list[Tree] args, void(list[value]) k) {
 Production p = ctx.definitions[s];
 if (args == []) {
   return;
 }
 println("Found prod: <p>");
 toctx(ctx, p, args[0], void(node n) {
   k([n]);
 });
} 
 

void toctx(type[&C<:node] ctx, label(_,  Symbol s), list[Tree] args, void(list[value]) k) 
  = toctx(ctx, s, args, k);

default void toctx(type[&C<:node] ctx, Symbol s, list[Tree] args, void(list[value]) k) {
  if (args == []) {
    println("No args left, but still need <s>");
    return;
  }
  println("Matching <s> against a <args[0].prod>");
  if (match(s, args[0])) {
    println("matched: <s>, <args[0].prod>");
    k([args[0]]);
  }
  println("fail from symbol");
}

void toctx(type[&C<:node] ctx, cons(label(str name, _), list[Symbol] syms, _, _), Tree t, void(node) k) {
  if (name == "hole") {
    println("******************* creating hole for : <t>");
    h = make(ctx, name, [t]);
    println(ctx2str(h));
    k(h);
    return;
  }
  println("cons for <name>");
  if (label(name, _) := t.prod.def) {
    println("Found it");
    for (x <- astArgs(t)) {
      println("AST arg: <x>");
    }
    toctx(ctx, syms, astArgs(t), void(list[value] args) {
      println("Make cons <name>(<syms>)");
      println("ARGS:");
      for (v <- args) {
       if (list[value] l := v) {
         println("   [<intercalate(", ", ["<x>" | value x <- l ])>]");
       }
       else {
         println("   <v> ");
       }
      }
      println("size of args <size(args)>");
      
      &C thing = make(ctx, name, args);
      if (list[Value] a1 := args[0], E a2 := args[1], list[Expr] a3 := args[2]) {
        println("Matched!");
        println(apply);
        thing = apply(a1, a2, a3);
      } 
      println(ctx2str(thing));
      k(thing);
    }); 
  }
  println("fail from cons");
}

void toctx(type[&C<:node] ctx, choice(_, set[Production] alts), Tree t, void(node) k) {
  println("choice");
  for (Production a <- alts) {
    toctx(ctx, a, t, k);
  } 
}

list[&C] toCtx(type[&C<:node] ctx, Tree t) {
  cs = [];
  
  toctx(ctx, ctx.definitions[ctx.symbol], t, void(node n) {
    println("****** SUCCESS: <ctx2str(n)>");
    cs += [typeCast(ctx, n)];
  });
  
  return cs;
}

  

list[&C] implode2ctx(type[&C<:node] ctx, Tree t) {
  sym = ctx.symbol;
  alts = ctx.definitions[sym].alternatives;
  cands = [];
 
 
  println("t.prod = <t.prod>");

  list[Tree] targs = flatten(t.args);
  
  for (c:\cons(label(str name, _), list[Symbol] syms, _, _) <- alts) {
    println("Trying <c>");
    
    if (name == "hole") {
      cands += [make(ctx, name, [t])];
      continue;
    }

    if (label(str prodLabel, _) := t.prod.def, name != prodLabel) {
      println("Wrong alt: <name> for <prodLabel>");
      continue;
    }
    int i = 0;
    int j = 0;
    list[value] args = [];
    while (i < size(syms)) {
      Symbol cur = syms[i];
      if (label(_, Symbol s) := cur) {
        cur = s;
      }
      println("CUR = <cur>");
      //println("targ = \"<targs[j]>\"");
      
      if (j < size(targs), char(_) := targs[j]) {
        println("char");
        j += 2;
        continue;
      }
      
      if (j < size(targs), !(targs[j] has prod)) {
        println("no prod");
        j += 2;
        continue;
      }
      
      if (j < size(targs), lit(_) := targs[j].prod.def) {
        println("lit");
        j += 2;
        continue;
      }

      if (j < size(targs), cur == sym) {
        // todo: backtracking
        args += implode2ctx(ctx, targs[j])[0];
        j += 2;
      }      
      
      if (\list(Symbol eltSym) := cur) {
        println("List: <eltSym>");
        list[value] elts = [];
        
        while (true) {
          if (j >= size(targs)) {
            break;
          }
          if (!(targs[j] has prod) || lit(_) := targs[j].prod.def) {
            j += 2;
            continue;
          }
          if (!match(eltSym, targs[j])) {
            break;
          }
          println("ElTsym: <eltSym>, <targs[j]>");
          elts += targs[j];
          j += 2;
        }
        args += [elts];
      }

      i += 1;
    }

    println("ARGS: <args>");
    for (value a <- args) {
      println("ARG: <a>");
    }
    //if (i == size(syms), j == size(t.args)) {
      cands += [make(ctx, name, args)];
    //}
  } 
  return cands; 
}

