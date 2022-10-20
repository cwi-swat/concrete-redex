module lang::credex::ParseRedex

import ParseTree;
import List;
import Set;
import Type;
import IO;

extend lang::credex::TraceRedex;

import lang::credex::util::Parenthesize;
import Exception;

/*
 * Applying reduction relations
 */

alias CR = rel[Tree context, Tree reduct]; // context reduct pairs

alias RRRR = rel[Tree redex, Tree reduct, str rule, Tree result];

RRRR applyWithRedex(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules, bool debug = false)
  = { <rx, rt, r, typeCast(#Tree, plug(tt, ctx2, rt))> |
     <&C ctx1, Tree rx> <- warnIfNonUnique(split(ct, t), debug),
     str r <- rules,
     <&C ctx2, Tree rt> <- red(r, ctx1, rx) }; //,


//@doc{Apply the reduction relation `red` to tree `t` trying all rules, decomposing `t` according to `ct`.
//The result is an `RR` which is relation from str (applied rule) to Tree (result).}
//RR apply(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C, Tree) red, Tree t, set[str] rules, bool debug = false)
//  = { <r, typeCast(#Tree, plug(tt, ctx2, rt))> |
//     <&C ctx1, Tree rx> <- warnIfNonUnique(split(ct, t), debug),
//     str r <- rules,
//     <&C ctx2, Tree rt> <- red(r, ctx1, rx) }; //,
//     //!debug || bprintln("<rx> === <r> ===\> <rt>") };


RR apply(type[Tree] ct, type[Tree] tt, CR(str,Tree, Tree) red, Tree t, set[str] rules, bool debug = false) {
  RR result = {};
  //println("Applying to <t>");
  for (<Tree ctx1, Tree rx> <- split(ct, t), str r <- rules, <Tree ctx2, Tree rt> <- red(r, ctx1, rx)) {
    if (debug) {
      println("rule = <r>, redex = <rx>, reduct = <rt>");
    }
    result += {<r, typeCast(#Tree, plug(tt, ctx2, rt))>};
  } 
  return result;
}

      
R reduce(type[&C<:Tree] ct, type[&T<:Tree] tt, CR(str,&C<:Tree, Tree) red, Tree t, set[str] rules)
  = apply(ct, tt, red, t, rules)<1>;



rel[&C<:Tree, Tree] warnIfNonUnique(rel[&C<:Tree, Tree] decomps, bool debug) {
  if (debug, size(decomps) > 1) {
    println("WARNING: non unique decomposition");
    for (<&C<:Tree ctx, Tree rx> <- decomps) {
      println("CTX: <ctx>");
      println("RDX: <rx>");
    }
  }
  return decomps;
}

 
@doc{Checking context grammars: ensure that every context has exactly one hole}
bool checkContext(type[&C<:Tree] ct) = true; // todo


/*
 * Split and plug
 */
 
 &T<:Tree myUnparen(type[&T<:Tree] typ, &T<:Tree t) {
  return  visit (t) {
    case appl(prod(Symbol s, list[Symbol] defs, set[Attr] attrs), list[Tree] args) =>
      appl(prod(s, defs[2..-2], attrs), args[2..-2])
        when !(s is lex), lit("⟨") in defs
    case appl(prod(Symbol s, list[Symbol] defs, set[Attr] attrs), list[Tree] args) =>
      appl(prod(s, defs[1..-1], attrs), args[1..-1])
        when s is lex, lit("⟨") in defs
  }
}

&T<:Tree debracket(type[&T<:Tree] typ, &T<:Tree t) {
  return t;
  return  visit (t) {
    case appl(prod(_, _, {\bracket(), *_}), list[Tree] args) => args[2]
  }
}

void splitPrint(type[&T<:Tree] ctxType, Tree t) {
  for (<Tree ctx, Tree rx> <- split(ctxType, t)) {
    println("<ctx> [ <rx> ]");
  }
}

@doc{Split a term according to the provided context grammar}
rel[Tree,Tree] split(type[&T<:Tree] ctxType, Tree t) {
  //println("split: <t>");
  try {
    ctx = parse(ctxType, "<t>", t@\loc, allowAmbiguity=true);
    rel[Tree, Tree] result = {};
    flattenAmbs(ctx, (Tree alt, Tree redex) {
      result += {<debracket(ctxType, alt), debracket(ctxType, redex)>};
    });
    return result;
  }
  catch ParseError(loc l): {
    //println("parse error");
    return {};  // stuck
  }
}

private bool isHole(Tree t) 
  = \tag("hole"()) in t.prod.attributes || \tag("redex"()) in t.prod.attributes
  when
    t has prod, t.prod has attributes;

private default bool isHole(Tree t) = false; 

void flattenAmbs(Tree t, void(Tree,Tree) k) {
  if (isHole(t)) { 
    k(makeHole(t.prod.def, t@\loc), t); 
    return;
  }
  
  switch (t) {
    case appl(Production p, list[Tree] args): {
      for (int i <- [0..size(args)]) {
        flattenAmbs(args[i], (Tree ctx, Tree redex) {
          k(appl(p, args[0..i] + [ctx] + args[i+1..])[@\loc=t@\loc], redex); 
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

@doc{Create a "fake" representation of a hole.}
Tree makeHole(Symbol sym, loc l) 
  = appl(prod(sym,[lit("☐")],{\tag("hole"())}),[
      appl(prod(lit("☐"),[\char-class([range(9744,9744)])],{}),[char(9744)])])[@\loc=l];
 


@doc{Plug reduct back into context, turning it into a term.
This function uses parsing to be type/syntax safe again in the result.}
&T plug(type[&T<:Tree] tt, Tree ctx, Tree reduct) {
  Tree t = plugTree(ctx, reduct);
  return parse(tt, "<t>");
}


str getSort(label(_, sort(str name))) = name; 
str getSort(sort(str name)) = name; 
default str getSort(Symbol _) = "";

@doc{Determine if a Tree is a context}
bool isContext(Tree t) = /^[A-Z]$/ := getSort(t.prod.def) || isHole(t);

@doc{Plugging the reduct back into a context (NB: *not* syntax safe).
Handcoded, because visit is too slow.}
Tree plugTree(Tree ctx, Tree reduct) {
  assert isContext(ctx) : "plug not traversing context <ctx>";

  if (isHole(ctx)) {
    return reduct;
  }
  if (appl(Production p, list[Tree] args) := ctx, int i <- [0..size(args)], isContext(args[i])) {
    return appl(p, args[0..i] + [plugTree(args[i], reduct)] + args[i+1..])[@\loc=ctx@\loc];
  }
  
  assert false:  "no hole found: <ctx>";
}


