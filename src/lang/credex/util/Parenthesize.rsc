module lang::credex::util::Parenthesize

import Type;
import Grammar;
import ParseTree;
import List;
import IO;
import String;

import lang::rascal::format::Grammar;


str openParen() = "⟨";
str closeParen() = "⟩";


void writeParenGrammar(type[&T<:Tree] typ, str name, loc path) {
  str src = "module <name>
            '<grammar2rascal(grammar({}, parenthesize(typ)))>";
  writeFile(path[path=path.path + "/" + split("::", name)[-1] + ".rsc"], src);
  
  src = "module Parse<name>
        '
        'import <name>;
        'import ParseTree;
        '
        '<symbol2rascal(typ.symbol)> parse(str src, loc l)
        '  = parse(#<symbol2rascal(typ.symbol)>, src, l);";
        
  writeFile(path[path=path.path + "/" + "Parse" + split("::", name)[-1] + ".rsc"], src); 
}

//type[Tree]
map[Symbol, Production] parenthesize(type[&T<:Tree] typ) {
   
   defs = typ.definitions;
   
   return ( s : parenProd(defs[s]) | Symbol s <- defs ); 
}


Production parenProd(p:choice(Symbol s, set[Production] alts))
  = (s is lex || s is \layouts) ? p : choice(s, { parenProd(p) | Production p <- alts, p.def != empty() });

Production parenProd(priority(Symbol s, list[Production] ps))
  = parenProd(choice(s, { p | Production p <- ps }));

Production parenProd(associativity(Symbol s, _, set[Production] ps))
  = parenProd(choice(s, ps));

Production parenProd(p:prod(\start(Symbol s), _, _)) 
  = p[def=\start(s)];
  
Production parenProd(p:prod(lex(_), _, _)) = p;

Production parenProd(p:prod(layouts(_), list[Symbol] _, _)) = p;

Production parenProd(prod(label(str l, Symbol s), list[Symbol] ss, set[Attr] attrs)) 
  = prod(label(l, s2), ss2, attrs)
  when 
    prod(Symbol s2, list[Symbol] ss2, _) := parenProd(prod(s, ss, attrs));

default Production parenProd(prod(Symbol s, list[Symbol] syms, set[Attr] attrs))
  = prod(s, [lit(openParen()),  *syms, lit(closeParen())], attrs);




str parenYield(appl(prod(label(_, \start(_)), list[Symbol] syms, _), list[Tree] args))
  = "<args[0]><( "" | it + parenYield(a) | Tree a <- args[1..-1] )><args[-1]>";

str parenYield(appl(prod(\start(_), list[Symbol] syms, _), list[Tree] args))
  = "<args[0]><( "" | it + parenYield(a) | Tree a <- args[1..-1] )><args[-1]>";

str parenYield(appl(prod(label(_, sort(_)), list[Symbol] syms, set[Attr] attrs), list[Tree] args))
  = "<openParen()><( "" | it + parenYield(a) | Tree a <- args )><closeParen()>";

str parenYield(appl(prod(sort(_), _, _), list[Tree] args))
  = "<openParen()><( "" | it + parenYield(a) | Tree a <- args )><closeParen()>";

str parenYield(appl(regular(_), list[Tree] args))
  = ( "" | it + parenYield(a) | Tree a <- args );


default str parenYield(Tree t) = "<t>";


&T<:Tree unparen(type[&T<:Tree] typ, Tree pt)
  = typeCast(typ, unparen(pt));

Tree unparen(appl(prod(label(str l, \start(Symbol s)), list[Symbol] syms, set[Attr] attrs), list[Tree] args)) 
  = appl(prod(label(l, \start(s)), syms, attrs), [args[0]] + [ unparen(a) | Tree a <- args[1..-1] ] + [args[-1]]);

Tree unparen(appl(prod(\start(Symbol s), list[Symbol] syms, set[Attr] attrs), list[Tree] args)) 
  = appl(prod(\start(s), syms, attrs), [args[0]] + [ unparen(a) | Tree a <- args[1..-1] ] + [args[-1]]);

Tree unparen(appl(prod(sort(str n), list[Symbol] syms, set[Attr] attrs), list[Tree] args)) 
  = appl(prod(sort(n), syms[2..-2], attrs), [ unparen(a) | Tree a <- args[2..-2] ]);

//Tree unparen(appl(prod(sort(str n), list[Symbol] syms, set[Attr] attrs), list[Tree] args)) 
//  = appl(prod(sort(n), syms, attrs), [ unparen(a) | Tree a <- args ])
//  when size(args) == 1;

Tree unparen(appl(prod(label(str l, sort(str n)), list[Symbol] syms, set[Attr] attrs), list[Tree] args)) 
  = appl(prod(label(l, sort(n)), syms[2..-2], attrs), [ unparen(a) | Tree a <- args[2..-2] ]);

Tree unparen(appl(regular(Symbol s), list[Tree] args))
  = appl(regular(s), [ unparen(a) | Tree a <- args ]);

default Tree unparen(Tree t) = t;



////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

// TODO: layout between paren and rest?
// Remove the layout nodes, after parsing, over the p-grammar
// after and before the parens.

Tree parenTree(Tree t) {
  return top-down-break visit (t) {
    case appl(p:prod(label(str l, Symbol s), list[Symbol] syms, set[Attr] attrs), list[Tree] args)
      => appl(parenProd(p), args2)
      when appl(_, list[Tree] args2) := parenTree(appl(prod(s, syms, attrs), args))
  
    case appl(p:prod(\start(_), list[Symbol] syms, _), list[Tree] args)
      => appl(p, args[0] + [ parenTree(a) | Tree a <- args[1..-1] ] + [ args[-1] ])
      
    case appl(p:prod(sort(_), _, _), list[Tree] args)
      => appl(parenProd(p), [ char(c) | int c <- chars(openParen()) ] 
           + [ parenTree(a) | Tree a <- args ] 
           + [ char(c) | int c <- chars(closeParen()) ])
  }

}



/*

Contract is

t = parse(g, src)
t' = paren(t)
g' = parenGrammar(g)
src' = unparse(t')
t'' = parse(g', src')
unparen(t'') == t

unparen(parse(parenGrammar(g), unparse(paren(parse(g, src))))) = parse(g, src)

*/




