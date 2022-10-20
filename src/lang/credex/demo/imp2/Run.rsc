module lang::credex::demo::imp2::Run

import lang::credex::demo::imp2::Semantics;
import lang::credex::demo::imp2::Conf;
import lang::credex::demo::imp2::Syntax;
import IO;

R reduceImp(Conf c) = reduce(#C, #Conf, red, c, {"leq", "seq1", "seq2", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 

RR applyImp(Conf c) = apply(#C, #Conf, red, c, {"leq", "seq1", "seq2", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 


TR traceImp(Conf c, bool debug=false) = trace(applyImp, c, debug=debug); 


void redexStepsImp(Conf e) {
  println("<e>");
  redexStepsImp_(e);
}

void redexStepsImp_(Conf e, str indent = "") {
  //println("E: <e>");
  if ((Conf)`<State _> ⊢ skip` := e) {
    return;
  }

  RR rr = applyImp(e);
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(rr) - 1 ? last : other> ";
    
  for (<str rule, Conf sub> <- rr) {
    println("<indented("└─", "├─")><e> \u001b[34m─<rule>→\u001b[0m <sub>");
    redexStepsImp_(sub, indent = indented(" ", "│"));
    i += 1;
  }
}

Conf example() 
  = (Conf)`[x ↦ 0, y ↦ 0] ⊢ 
          '  x := 1; 
          '  y := x + 2; 
          '  if x \<= y then 
          '    x := x + y 
          '  else 
          '    y := 0 
          '  fi`;

Stmt exampleStmt() 
  = (Stmt)`x := 1 + 2; 
          '  y := x + 2; 
          '  if x \<= y then 
          '    x := x + y 
          '  else 
          '    y := 0 
          '  fi`;

Conf primes(int n) 
  = (Conf)
`[i ↦ 0 , m ↦ 0, n ↦ 0, q ↦ 0, r ↦ 0, s ↦ 0, t ↦ 0, x ↦ 0, y ↦ 0, z ↦ 0 ] ⊢ 
'm := <Int x>;  n := 2;
'while n \<= m do
'  i := 2;  q := n/i;  t := 1;
'  while i\<=q and 1\<=t do
'    x := i;
'    y := q;
'    z := 0;
'    while not x \<= 0 do
'      q := x/2;
'      r := q+q+1;
'      if r \<= x then z := z+y else skip fi;
'      x := q;
'      y := y+y
'    od;
'    if n \<= z then t := 0 else i := i+1; q := n/i fi
'  od; 
'  if 1 \<= t then s := s+1 else skip fi;
'  n := n+1
'od`
  when Int x := [Int]"<n>";