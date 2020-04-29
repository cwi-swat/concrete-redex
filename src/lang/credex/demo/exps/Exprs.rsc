module lang::credex::demo::exps::Exprs

extend lang::std::Layout;

extend lang::credex::ParseRedex; // extend because parse bug
import lang::credex::util::Parenthesize;
import lang::credex::util::GenSen;
import lang::credex::util::Rebracket;

import lang::rascal::grammar::definition::Priorities;

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
  = bracket "(" E ")"
  | E "*" Expr
  | Expr "*" E
  | E "-" Expr
  | Num "-" E
  | @hole "(" Num ")" 
  | @hole Num "*" Num
  | @hole Num "-" Num
  ;
 
Expr wrap(Expr e) {
  return (Expr)`(<Expr e>)`;
}
 
 
E parenE((E)`<E e> * <Expr ex>`) = (E)`(<E e2> * <Expr ex2>)`
  when
    E e2 := parenE(e),
    Expr ex2 := parenExpr(ex);

E parenE((E)`<Expr ex> * <E e>`) = (E)`(<Expr ex2> * <E e2>)`
  when
    Expr ex2 := parenExpr(ex),
    E e2 := parenE(e);
    
E parenE((E)`<E e> - <Expr ex>`) = (E)`(<E e2> - <Expr ex2>)`
  when
    bprintln("Yes"),
    E e2 := parenE(e),
    Expr ex2 := parenExpr(ex);

E parenE((E)`<Num n> - <E e>`) = (E)`(<Num n> - <E e2>)`
  when
    bprintln("Yes num"),
    E e2 := parenE(e);
    
E parenE((E)`<Num n1> * <Num n2>`) = (E)`(<Num n1> * <Num n2>)`;

E parenE((E)`<Num n1> - <Num n2>`) = (E)`(<Num n1> - <Num n2>)`;


default E parenE(E e) = e
  when bprintln("Default: <e>");

str parenE2(appl(prod(sort("E"), _, _), list[Tree] args))
  = "(" + ( "" | it + parenE2(a) | Tree a <- args ) + ")";

str parenE2(appl(prod(sort("Expr"), _, _), list[Tree] args))
  = "(" + ( "" | it + parenE2(a) | Tree a <- args ) + ")";

default str parenE2(Tree t) = "<t>";
 
Expr rebracket(e:(Expr)`<Expr l> * <Expr r>`)
  = (Expr)`<Expr l2> * <Expr r2>` 
  when //bprintln("mul: <l> - <r>"),
    //bprintln("e = <e>, l = <l>, rebracket(l) = <rebracket(l)>"),
    Expr ll := rebracket(l),
    //bprintln("ll = <ll>"),
    Expr(Expr) ff := Expr(Expr bla) { return wrap(bla); },
    //bprintln("ff = <ff>"),
    Expr l2 := parens(myPrios, e, l, ll, ff),
    //bprintln("l2 = <l2>"),
    //bprintln("e = <e>, r = <r>, rebracket(r) = <rebracket(r)>"),
    Expr rr := rebracket(r),
    Expr r2 := parens(myPrios, e, r, rr, ff);

public DoNotNest myPrios = getPrios(#Expr);

Expr rebracket(e:(Expr)`<Expr l> - <Expr r>`)
  = (Expr)`<Expr l2> - <Expr r2>` 
  when //bprintln("sub: <l> - <r>"),
    //bprintln("e = <e>, l = <l>, rebracket(l) = <rebracket(l)>"),
    Expr ll := rebracket(l),
    //bprintln("ll = <ll>"),
    Expr(Expr) ff := Expr(Expr bla) { return wrap(bla); },
    //bprintln("ff = <ff>"),
    Expr l2 := parens(myPrios, e, l, ll, ff),
    //bprintln("l2 = <l2>"),
    //bprintln("e = <e>, r = <r>, rebracket(r) = <rebracket(r)>"),
    Expr rr := rebracket(r),
    Expr r2 := parens(myPrios, e, r, rr, ff);
    
default Expr rebracket(Expr e) = e;
 
Expr parenExpr((Expr)`<Expr l> * <Expr r>`)  
  = (Expr)`(<Expr l2> * <Expr r2>)`
  when Expr l2 := parenExpr(l),
    Expr r2 := parenExpr(r);
   
Expr parenExpr((Expr)`<Expr l> - <Expr r>`)  
  = (Expr)`(<Expr l2> - <Expr r2>)`
  when Expr l2 := parenExpr(l),
    Expr r2 := parenExpr(r);

Expr parenExpr((Expr)`(<Expr e>)`)  
  = parenExpr(e);

default Expr parenExpr(Expr e) = e;

Expr unparenExpr((Expr)`(<Expr l> * <Expr r>)`)
  = (Expr)`<Expr l> * <Expr r>`;
  
Expr unparenExpr((Expr)`(<Expr l> - <Expr r>)`)
  = (Expr)`<Expr l> - <Expr r>`;

Expr unparenExpr((Expr)`(<Num n>)`)
  = (Expr)`<Num n>`;
  
default Expr unparenExpr(Expr e) = e;

void showTheExample() {
  Expr e1 = (Expr) `1 - 2 - (3 - 3)`;
  println("## Only single decomposition");
  process(e1);
  
  println("");
  Expr e2 = (Expr) `1 * 2 * (3 * 3)`;
  println("## Two decompositions");
  process(e2);
  
}

RR applyExprFix(Expr e) {
  pe = parenExpr(e);
  E ctx = parse(#E, "<pe>", allowAmbiguity=true); 

  RR result = {};

  flattenAmbs(ctx, void(Tree alt, Tree redex) {
  
    // remove all parentheses 
    alt = debracket(#E, alt);
    redex = debracket(#E, redex);
    
    for (str r <- {"mul", "par", "sub"}, <E ctx, Expr rt> <- red(r, alt, redex) ) {
       if (E ctx2 := plugTree(ctx, rt)) {
         
         // add parentheses to the plugged context 
         str pctx = parenE2(ctx2);
         
         // parse it to obtain an Expr
         newExpr = parse(#Expr, pctx);
         
         // remove all brackets, and insert necessary ones.
         result += {<r, rebracket(debracket(#Expr, newExpr))>};
       }
       else {
         assert false: "bad plug";
       }
    }
  });
  
  return result;
}

void process(Expr e) {
  println("The term: <e>");
  pe = parenExpr(e);
  println("With parens: <pe>");
  
  E ctx = parse(#E, "<pe>", allowAmbiguity=true); 

  println("Splitting: "); 
  int i = 0;
  flattenAmbs(ctx, void(Tree alt, Tree redex) {
    println("DECOMPOSITION #<i>");
    i += 1;
    println(" before debracket: ");
    println("  - ctx: <alt>, redex = <redex>");
    println(" after debracket: ");
    alt = debracket(#E, alt);
    redex = debracket(#E, redex);
    println("  - ctx:  <alt>, redex = <redex>");
    RR result = {};
    for (str r <- {"mul", "par", "sub"}
      , <E ctx, Expr rt> <- red(r, alt, redex) ) {
       if (E ctx2 := plugTree(ctx, rt)) {
         println("After plug: <ctx2>");
         str pctx = parenE2(ctx2);
         println("Parened ctx: <pctx>");
         newExpr = parse(#Expr, pctx);
         println("parsed as expr: <newExpr>");
         result += {<r, newExpr>};
       }
       
    }
    for (<str r, Expr t> <- result) {
      println("reduction via <r>: <t>");
      println(" - with parens: <t> ");
      println(" - without <debracket(#Expr, t)>");
      println(" - rebracketed <rebracket(debracket(#Expr, t))>");
    }
  });
  
  
}

  
// parenthesized ctx grammar
//syntax E 
//  = "⟨" "(" E ")" 
//  | "⟨" E "*" ExprP "⟩"
//  | "⟨" ExprP "*" E "⟩"
//  | "⟨" E "-" ExprP "⟩"
//  | "⟨" NumP "-" E "⟩"
//  | @hole "⟨" "(" NumP ")" "⟩"
//  | @hole "⟨" NumP "*" NumP "⟩"
//  | @hole "⟨" NumP "-" NumP "⟩"
//  ;
  
// and the base grammar (NB: no more prio/assoc)
//syntax ExprP
//  = "⟨" Num "⟩" 
//  | "⟨" "(" ExprP ")" "⟩"
//  | "⟨" ExprP "*" ExprP "⟩"
//  | "⟨" ExprP "-" ExprP "⟩"
//  ;
  
//lexical NumP
//  = "⟨" [\-]?[1-9][0-9]* "⟩"
//  | "⟨" [0] "⟩"
//  ;
  
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

void testParens() {
  for (int i <- [0..100]) {
    if (Expr e := genSen(#Expr, 5)) {
      println("SRC: <e>");
      e = parenExpr(parse(#Expr, "<e>"));
      println("PAR: <e>");
      if (!isVal(e)) {
        split(e);
	  }      
    }
    
  }
}

void testIt(int depth=5, int tries=10) {
  for (int i <- [0..tries]) { 
    t = genSen(#Expr, depth);
    println("Expr: <t>");
    e = parse(#Expr, "<t>");
    int evalResult = eval(e);
    int stepsResult = steps(e);
    set[int] redexResults = redex(e);
    println(" - eval = <evalResult>");
    println(" - steps = <stepsResult>");
    println(" - redex = <redexResults>");
    if (evalResult != stepsResult) {
      throw "test failed";
    }
    if (evalResult != redex) {
      throw "test failed";
    }
  }
}

void printCtx(Tree ctx, Tree rx) {
    println("<ctx> [ <rx> ]");
}

void split(Expr e) {
   E ctx = parse(#E, "<e>", allowAmbiguity=true);
   println("# Splitting `<e>`"); 
   flattenAmbs(ctx, void(Tree alt, Tree redex) {
    printCtx(alt, redex);
  });
}

void theScript() {
  src = "(2 - 1) * (4 - 3 - 1)";
  //src = "1 - 2 * 3";
  println("Source: <src>");
  Expr e = parse(#Expr, src); // not amb
  E ctx = parse(#E, src, allowAmbiguity=true); // includes bad amb



  println("# Split with bad amb");  
  flattenAmbs(ctx, void(Tree alt, Tree redex) {
    printCtx(alt, redex);
  });

  
  psrc = "<parenExpr(e)>";
  ctx = parse(#E, psrc, allowAmbiguity=true); // only one amb


  println("# Split with parens");  
  flattenAmbs(ctx, void(Tree alt, Tree redex) {
    printCtx(alt, redex);
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

void redexSteps(Expr e, str indent = "", RR(Expr) applyExpr = applyExpr) {
  RR rr = applyExpr(e);
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(rr) - 1 ? last : other> ";
    
  for (<str rule, Expr sub> <- rr) {
    println("<indented("└─", "├─")><e> \u001b[34m─<rule>→\u001b[0m <sub>");
    redexSteps(sub, indent = indented(" ", "│"));
    i += 1;
  }
}

     
     