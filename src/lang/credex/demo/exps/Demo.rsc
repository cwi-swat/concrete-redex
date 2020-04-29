module lang::credex::demo::exps::Demo

import lang::credex::demo::exps::Exprs;

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

/*
 * Parenthesize an expression
 */

Expr parenExpr((Expr)`<Expr l> * <Expr r>`)  
  = (Expr)`(<Expr l2> * <Expr r2>)`
  when Expr l2 := parenExpr(l),
    Expr r2 := parenExpr(r);
   
Expr parenExpr((Expr)`<Expr l> - <Expr r>`)  
  = (Expr)`(<Expr l2> - <Expr r2>)`
  when Expr l2 := parenExpr(l),
    Expr r2 := parenExpr(r);

Expr parenExpr((Expr)`(<Expr e>)`)  
  = (Expr)`(<Expr e2>)`
  when Expr e2 := parenExpr(e);

default Expr parenExpr(Expr e) = e;

/*
 * Unparse a context E with parentheses
 */

str parenE(appl(prod(sort("E"), _, _), list[Tree] args))
  = "(" + ( "" | it + parenE(a) | Tree a <- args ) + ")";

str parenE(appl(prod(sort("Expr"), _, _), list[Tree] args))
  = "(" + ( "" | it + parenE(a) | Tree a <- args ) + ")";

default str parenE(Tree t) = "<t>";

 

// helper function to wrap an expression in parentheses
Expr wrap(Expr e) {
  return (Expr)`(<Expr e>)`;
}

/*
 * Rebracket: insert parentheses in an expression where needed
 */ 
 
public DoNotNest myPrios = getPrios(#Expr);
 
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
 
/*
 * A fixed applyExpr which prevents spurious ambiguities when splitting
 */

RR applyExprFix(Expr e) {
  // add parentheses everywhere
  pe = parenExpr(e);
  
  //println("Applying <e> (with parens: <pe>)");
  E ctxForest = parse(#E, "<pe>", allowAmbiguity=true); 

  RR result = {};

  flattenAmbs(ctxForest, void(Tree ctx, Tree redex) {
  
    // remove all parentheses 
    ctx = debracket(#E, ctx);
    redex = debracket(#E, redex);
    
    for (str r <- {"mul", "par", "sub"}, <E ct, Expr rt> <- red(r, ctx, redex) ) {
       // plug the reduct back into the context
       Tree pt = plugTree(ct, rt);
       
       // add parentheses to the plugged context 
       str pctx = parenE(pt);
         
       // parse it to obtain an Expr
       Expr newExpr = parse(#Expr, pctx);
         
       // remove all brackets, and insert necessary ones.
       result += {<r, rebracket(debracket(#Expr, newExpr))>};
    }
  });
  
  return result;
}


/*
 * Redex: evaluate an expression using Credex
 * (using the fixed applyExpr)
 */

set[int] redex(Expr e) {
  if (isVal(e)) {
    return {toInt("<e>")};
  }
  RR r = applyExprFix(e);
  return ( {} | it + redex(sub) | <_, Expr sub> <- r );
}


void badAndGood() {
  
}

void show(Expr e) {

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
         str pctx = parenE(ctx2);
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

void testIt(int depth=4, int tries=10) {
  for (int i <- [0..tries]) { 
    t = genSen(#Expr, depth);
    println("Expr: <t>");
    e = parse(#Expr, "<t>");
    int evalResult = eval(e);
    int stepsResult = steps(e);
    set[int] redexResults = redex(e, applyExpr=applyExprFix);
    println(" - eval = <evalResult>");
    println(" - steps = <stepsResult>");
    println(" - redex = <redexResults>");
    if (evalResult != stepsResult) {
      throw "test failed";
    }
    if ({evalResult} != redexResults) {
      throw "test failed";
    }
  }
}




////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
/// try out code

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
         str pctx = parenE(ctx2);
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


void showTheExample() {
  Expr e1 = (Expr) `1 - 2 - (3 - 3)`;
  println("## Only single decomposition");
  process(e1);
  
  println("");
  Expr e2 = (Expr) `1 * 2 * (3 * 3)`;
  println("## Two decompositions");
  process(e2);
  
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

