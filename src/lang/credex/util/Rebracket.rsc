module lang::credex::util::Rebracket


import lang::rascal::grammar::definition::Priorities;
import Grammar;
import Node;
import IO;
import List;

import ParseTree;


// NB () are required around #Expression; otherwise ambiguous code error.
//public DoNotNest getOberon0Prios() = doNotNest(grammar({}, (#Expression).definitions));
//
//private DoNotNest PRIOS = getOberon0Prios();
//
//public DoNotNest oberon0Prios() = PRIOS;


DoNotNest getPrios(type[&T<:Tree] t) = doNotNest(grammar({}, t.definitions));

&T<:Tree parens(DoNotNest prios, &T<:Tree parent, &T<:Tree kid, &T<:Tree x, (&T<:Tree)(&T<:Tree) parenizer) {
  if (appl(Production pprod, list[Tree] pargs) := parent,
    appl(Production kprod, _) := kid,  <pprod, int pos, kprod> <- prios, pargs[pos] == kid) {
      return parenizer(x);
  }
  return x;
}

//Tree parens(DoNotNest prios, 
//  appl(Production pprod, list[Tree] pargs), 
//  kid:appl(Production kprod, _), Tree x, Tree(Tree) parenizer) = parenizer(x)
//  when 
//    bprintln(pprod),
//     <pprod, int pos, kprod> <- prios,
//     pargs[pos] == kid;
//
//default Tree parens(DoNotNest prios, Tree _, Tree _, Tree x, Tree(Tree) parenizer) = x
//  when bprintln("DEFAULT: <x>");


