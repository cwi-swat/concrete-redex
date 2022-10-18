module lang::credex::demo::exps::Exprs

extend lang::std::Layout;

extend lang::credex::ParseRedex; // extend because parse bug

import IO;
import Set;
import String;
import ParseTree;


syntax Expr
  = Num
  | bracket "(" Expr ")"
  | assoc Expr "*" Expr
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
  | @hole Num
  ;
 



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
 
 // TODO: this should go.
 CR red("par", E e, (E)`(<Num n>)`) 
  = {<e, (Expr)`<Num n>`>};

 CR red("mul", E e, (E)`<Num n1> * <Num n2>`)
  = {<e, [Expr]"<toInt(n1) * toInt(n2)>">};

CR red("sub", E e, (E)`<Num n1> - <Num n2>`)
  = {<e, [Expr]"<toInt(n1) - toInt(n2)>">};

default CR red(str _, E _, Tree _) = {};

RR applyExpr(Expr e) = apply(#E, #Expr, red, e, {"mul", "sub", "par"});

void redexSteps(Expr e, str indent = "") {
  if (isVal(e)) {
    return;
  }

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

     
     