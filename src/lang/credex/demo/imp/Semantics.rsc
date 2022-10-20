module lang::credex::demo::imp::Semantics

import lang::credex::demo::imp::Contexts;
extend lang::credex::ParseRedex;
import String;
import IO;


R reduceImp(Conf c) = reduce(#C, #Conf, red, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 

RR applyImp(Conf c) = apply(#C, #Conf, red, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 


TR traceImp(Conf c, bool debug=false) = trace(applyImp, c, debug=debug); 


default CR red(str _, C _, Tree _) = {};

CR red("lookup", C c, (A)`<Id x>`) = {<c, (AExp)`<Int i>`>}
  when 
    isDefined(x, c.state), 
    Int i := lookup(x, c.state); 


CR red("add", C c, (A)`<Int i1> + <Int i2>`) = {<c, (AExp)`<Int i>`>} 
  when
    int n1 := toInt("<i1>"), int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 + n2>";

CR red("div", C c, (A)`<Int i1> / <Int i2>`) = {<c, (AExp)`<Int i>`>}
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 / n2>";


CR red("leq", C c, (B)`<Int i1> \<= <Int i2>`) = {<c, b ? (BExp)`true` : (BExp)`false`>}
  when 
    bool b := toInt("<i1>") <= toInt("<i2>");

CR red("not-false", C c, (B)`not false`) = {<c, (BExp)`true`>};

CR red("not-true", C c, (B)`not true`) = {<c, (BExp)`false`>};
  
CR red("and-true", C c, (B)`true and <BExp b>`) = {<c, b>};

CR red("and-false", C c, (B)`false and <BExp b>`) = {<c, (BExp)`false`>};

CR red("seq", C c, (S)`skip; <Stmt s2>`) = {<c, s2>};

CR red("if-true", C c, (S)`if true then <Stmt s1> else <Stmt s2> fi`) = {<c, s1>};

CR red("if-false", C c, (S)`if false then <Stmt s1> else <Stmt s2> fi`) = {<c, s2>};

CR red("while", C c, (S)`while <BExp b> do <Stmt s> od`)
  = {<c, (Stmt)`if <BExp b> then <Stmt s>; while <BExp b> do <Stmt s> od else skip fi`>};

CR red("assign", C c, (S)`<Id x> := <Int i>`) = {<c[state=s2], (Stmt)`skip`>}
  when 
    isDefined(x, c.state), 
    State s2 := update(x, i, c.state);

// bool isDefined(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
//   = true
//   when x == y;

bool isDefined(Id x, State s) {
  for ((VarInt)`<Id y> ↦ <Int i>` <- s.pairs) {
     if (y := x) {
       return true;
     }
  }
  return false;
}

Int lookup(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = i
  when x := y;
  
State update(Id x, Int i, (State)`[<{VarInt ","}* v1>, <Id y> ↦ <Int _>, <{VarInt ","}* v2>]`)
  = (State)`[<{VarInt ","}* v1>, <Id x> ↦ <Int i>, <{VarInt ","}* v2>]`
  when x := y;

Conf exampleLine() 
  = (Conf)`[x↦0,y ↦0] ⊢ x:=1; y:=x+2; if x\<=y then x:=x+y else y:=0 fi`;


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