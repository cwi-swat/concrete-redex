module lang::credex::demo::exps::Exprs

extend lang::std::Layout;

extend lang::credex::ParseRedex; // extend because parse bug
import lang::credex::util::Parenthesize;
import lang::credex::util::GenSen;

import IO;
import Set;
import String;
import ParseTree;
import vis::ParseTree;

syntax Expr
  = Num
  | bracket "(" Expr ")"
  | left Expr "*" Expr
  > left Expr "-" Expr
  ;
  
lexical Num
  = [\-]?[1-9][0-9]*
  | [0]
  ;
  
// context grammar  
syntax E
  = "(" E ")"
  | E "*" Expr
  | Expr "*" E
  | E "-" Expr
  | Num "-" E
  | @hole "(" Num ")" 
  | @hole Num "*" Num
  | @hole Num "-" Num
  ;
  
// parenthesized ctx grammar
syntax E 
  = "⟨" "(" E ")" "⟩"
  | "⟨" E "*" ExprP "⟩"
  | "⟨" ExprP "*" E "⟩"
  | "⟨" E "-" ExprP "⟩"
  | "⟨" NumP "-" E "⟩"
  | @hole "⟨" "(" NumP ")" "⟩"
  | @hole "⟨" NumP "*" NumP "⟩"
  | @hole "⟨" NumP "-" NumP "⟩"
  ;
  
// and the base grammar (NB: no more prio/assoc)
syntax ExprP
  // = "⟨" Num "⟩" don't do it for injections
  = "⟨" "(" ExprP ")" "⟩"
  | "⟨" ExprP "*" ExprP "⟩"
  | "⟨" ExprP "-" ExprP "⟩"
  ;
  
lexical NumP
  = "⟨" [\-]?[1-9][0-9]* "⟩"
  | "⟨" [0] "⟩"
  ;
  
/*
 * we have a non-amb expr pt
 * unparse with parens
 * parse over parenthesized ctx grammar
 * get forest
 * unparenthesize each tree
 * apply reductions
 * etc.
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

void testIt(int depth=5, int tries=10) {
  for (int i <- [0..tries]) { 
    t = genSen(#Expr, depth);
    println("Expr: <t>");
    e = parse(#Expr, "<t>");
    int evalResult = eval(e);
    int stepsResult = steps(e);
    //set[int] redexResults = redex(e);
    println(" - eval = <evalResult>");
    println(" - steps = <stepsResult>");
    //println(" - redex = <redexResults>");
    if (evalResult != stepsResult) {
      throw "test failed";
    }
    //if (evalResult != redex) {
    //  throw "test failed";
    //}
  }
}

void theScript() {
  src = "(2 - 1) * (4 - 3 - 1)";
  src = "1 - 2 * 3";
  println("Source: <src>");
  Expr e = parse(#Expr, src); // not amb
  E ctx = parse(#E, src, allowAmbiguity=true); // includes bad amb

  void printCtx(Tree ctx, Tree rx) {
    println("<ctx> [ <rx> ]");
  }


  println("# Split with bad amb");  
  flattenAmbs(ctx, void(Tree alt, Tree redex) {
    printCtx(alt, redex);
  });

  
  psrc = parenYield(e);
  ctx = parse(#E, psrc, allowAmbiguity=true); // only one amb


  println("# Split with parens");  
  flattenAmbs(ctx, void(Tree alt, Tree redex) {
    printCtx(alt, redex);
  });

  println("# Split with unparen");  
  flattenAmbs(ctx, void(Tree alt, Tree redex) {
    printCtx(myUnparen(#E, alt), myUnparen(#E, redex));
  });
  
}


/*
 * Big step (natural semantics/definitional interpreter)
 */
  
int eval((Expr)`<Num n>`) 
  = toInt("<n>");

int eval((Expr)`(<Expr e>)`) 
  = eval(e);

int eval((Expr)`<Expr l> * <Expr r>`) 
  = eval(l) * eval(r);

int eval((Expr)`<Expr l> - <Expr r>`) 
  = eval(l) - eval(r);

/*
 * Small step/reduction (express non-det for *, but only one path is ever taken)
 */

bool isVal(Expr e) = ((Expr)`<Num _>` := e);

int toInt(Num n) = toInt("<n>");

Expr step((Expr)`(<Expr e>)`) = e;

// either reduce left
Expr step((Expr)`<Expr l> * <Expr r>`) 
  = (Expr)`<Expr l2> * <Expr r>`
  when !isVal(l), Expr l2 := step(l);

// or right
Expr step((Expr)`<Expr l> * <Expr r>`) 
  = (Expr)`<Expr l> * <Expr r2>`
  when !isVal(r), Expr r2 := step(r);

// until both sides are numbers
Expr step((Expr)`<Num n1> * <Num n2>`) 
  = [Expr]"<toInt(n1) * toInt(n2)>";

// keep reducing left
Expr step((Expr)`<Expr l> - <Expr r>`) 
  = (Expr)`<Expr l2> - <Expr r>`
  when !isVal(l), Expr l2 := step(l);

// until it's a value, then reduce right
Expr step((Expr)`<Num n> - <Expr r>`) 
  = (Expr)`<Num n> - <Expr r2>`
  when !isVal(r), Expr r2 := step(r);

// until both are numbers
Expr step((Expr)`<Num n1> - <Num n2>`) 
  = [Expr]"<toInt(n1) - toInt(n2)>";
    
default Expr step(Expr e) = e; // done


// closure of `step`
int steps(Expr e, bool debug = false) {
   solve (e) {
     if (debug) {
       println(e);
     }
     e = step(e);
   }
   assert isVal(e): "stuck <e>"; 
   return toInt("<e>");
}



/*
 * Redex semantics
 * (how to deal with brackets?)
 */
 
 CR red("par", E e, (E)`(<Num n>)`) 
  = {<e, (Expr)`<Num n>`>};

 CR red("mul", E e, (E)`<Num n1> * <Num n2>`)
  = {<e, [Expr]"<toInt(n1) * toInt(n2)>">};

CR red("sub", E e, (E)`<Num n1> - <Num n2>`)
  = {<e, [Expr]"<toInt(n1) - toInt(n2)>">};

default CR red(str _, E _, Tree _) = {};

RR applyExpr(Expr e) = apply(#E, #Expr, red, e, {"mul", "sub", "par"});

set[int] redex(Expr e) {
  RR r = applyExpr(e);
  if (r == {}) {
    assert isVal(e): "stuck <e>";
    return {toInt("<e>")};
  }
  return ( {} | it + redex(sub) | <_, Expr sub> <- r );
}

void redexSteps(Expr e, str indent = "") {
  RR rr = applyExpr(e);
  int i = 0;
  for (<str rule, Expr sub> <- applyExpr(e)) {
    piece = i== size(rr) - 1 ? "└─" : "├─" ;  
    println("<indent> <piece> <e> \u001b[34m ─<rule>→\u001b[0m <sub>");
    // └ ├ │ ⋅
    piece = i== size(rr) - 1 ? "  " : "│ " ;  
    redexSteps(sub, indent = indent + " <piece>");
    i += 1;
  }
}

     
     