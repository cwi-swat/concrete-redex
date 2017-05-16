module paper::imp::Semantics

import paper::imp::Syntax;
import paper::MatchRedex;
import String;

syntax State = "[" {VarInt ","}* "]";
syntax VarInt = Id "↦" Int;
syntax Conf = conf: State "⊢" Stmt;


data AE(loc src = |tmp:///|)
  = add(AE ae, AExp aexp)
  | add(AExp aexp, AE ae)
  | div(AE ae, AExp aexp)
  | div(AExp aexp, AE ae)
  | hole(AExp aexp)
  ;
  
data BE(loc src = |tmp:///|)
  = leq(AE ae, AExp aexp)
  | leq(Int n, AE ae)
  | not(BE be)
  | and(BE be, BExp bexp)
  | hole(BExp bexp)
  ;
  
data S(loc src = |tmp:///|)
  = assign(Id var, AE ae)
  | seq(S s, Stmt stmt)
  | ite(BE be, Stmt then, Stmt els)
  | hole(Stmt stmt)
  ;
  
data C(loc src = |tmp:///|)
  = conf(State state, S s)
  ;
  

R reduceImp(Conf c) = reduce(#C, red, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}, #S, #BE, #AE); 

default CR red(str _, C _) = {};

CR red("lookup", C c:/hole((AExp)`<Id x>`))
  = {<c, (AExp)`<Int i>`>}
  when 
    isDefined(x, c.state), 
    Int i := lookup(x, c.state); 


CR red("add", C c:/hole((AExp)`<Int i1> + <Int i2>`)) = {<c, (AExp)`<Int i>`>} 
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 + n2>";

CR red("div", C c:/hole((AExp)`<Int i1> / <Int i2>`)) = {<c, (AExp)`<Int i>`>}
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 / n2>";


CR red("leq", C c:/hole((BExp)`<Int i1> \<= <Int i2>`)) = {<c, b ? (BExp)`true` : (BExp)`false`>}
  when 
    bool b := toInt("<i1>") <= toInt("<i2>");

CR red("not-false", C c:/hole((BExp)`not false`)) = {<c, (BExp)`true`>};

CR red("not-true", C c:/hole((BExp)`not true`)) = {<c, (BExp)`false`>};
  
CR red("and-true", C c:/hole((BExp)`true and <BExp b>`)) = {<c, b>};

CR red("and-false", C c:/hole((BExp)`false and <BExp b>`)) = <c, (BExp)`false`>;

CR red("seq", C c:/hole((Stmt)`skip; <Stmt s2>`)) = {<c, s2>};

CR red("if-true", C c:/hole((Stmt)`if true then <Stmt s1> else <Stmt s2> fi`)) = {<c, s1>};

CR red("if-false", C c:/hole((Stmt)`if false then <Stmt s1> else <Stmt s2> fi`)) = {<c, s2>};

CR red("while", C c:/hole((Stmt)`while <BExp b> do <Stmt s> od`))
  = {<c, (Stmt)`if <BExp b> then <Stmt s>; while <BExp b> do <Stmt s> od else skip fi`>};

CR red("assign", C c:/hole((Stmt)`<Id x> := <Int i>`)) = {<c[state=s2], (Stmt)`skip`>}
  when 
    isDefined(x, c.state), 
    State s2 := update(x, i, c.state);

bool isDefined(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = true
  when x == y;
  
Int lookup(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = i
  when x == y;
  
State update(Id x, Int i, (State)`[<{VarInt ","}* v1>, <Id y> ↦ <Int _>, <{VarInt ","}* v2>]`)
  = (State)`[<{VarInt ","}* v1>, <Id x> ↦ <Int i>, <{VarInt ","}* v2>]`
  when x == y;


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
