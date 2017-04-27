module IMPSemantics

import IMP;
extend RRedex;

import String;

syntax Ctx
  = Ctx "+" AExp
  | AExp "+" Ctx
  | Ctx "/" AExp
  | AExp "/" Ctx
  | Ctx "\<=" AExp
  | Int "\<=" Ctx // injections are possible :-)
  | "not" Ctx
  | Ctx "and" BExp
  | Id ":=" Ctx
  | Ctx ";" Stmt
  | "if" Ctx "then" Stmt "else" Stmt "fi"
  | "(" Ctx "," State state ")"
  ;
  
syntax State
  = "[" {VarInt ","}* "]";

syntax VarInt
  = Id "↦" Int
  ;

// we can't use labels, because plug etc. cannot know about it.  
syntax Conf
  = "(" Stmt "," State state ")";
  
  
Conf example() 
  = (Conf)`(x := 1; y := 2; if x \<= y then x := x + y else y := 0 fi, [x ↦ 0, y ↦ 0])`;

bool isDefined(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = true
  when x == y;
  
Int lookup(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = i
  when x == y;
  
State update(Id x, Int i, (State)`[<{VarInt ","}* v1>, <Id y> ↦ <Int _>, <{VarInt ","}* v2>]`)
  = (State)`[<{VarInt ","}* v1>, <Id x> ↦ <Int i>, <{VarInt ","}* v2>]`
  when x == y;


CR rule("add", Ctx c, (AExp)`<Int i1> + <Int i2>`) 
  = [<c, (AExp)`<Int i>`>]
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 + n2>";

CR rule("div", Ctx c, (AExp)`<Int i1> / <Int i2>`) 
  = [<c, (AExp)`<Int i>`>]
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 / n2>";


CR rule("leq", Ctx c, (BExp)`<Int i1> \<= <Int i2>`)
  = [<c, toInt("<i1>") <= toInt("<i2>") ? (BExp)`true` : (BExp)`false`>];

CR rule("not-false", Ctx c, (BExp)`not false`)
  = [<c, (BExp)`true`>];

CR rule("not-true", Ctx c, (BExp)`not true`)
  = [<c, (BExp)`false`>];
  
CR rule("and-true", Ctx c, (BExp)`true and <BExp b>`)
  = [<c, b>];

CR rule("and-false", Ctx c, (BExp)`false and <BExp b>`)
  = [<c, (BExp)`false`>];

CR rule("seq", Ctx c, (Stmt)`skip; <Stmt s2>`)
  = [<c, s2>];

CR rule("if-true", Ctx c, (Stmt)`if true then <Stmt s1> else <Stmt s2> fi`)
  = [<c, s1>];

CR rule("if-false", Ctx c, (Stmt)`if false then <Stmt s1> else <Stmt s2> fi`)
  = [<c, s2>];

CR rule("while", Ctx c, (Stmt)`while <BExp b> do <Stmt s> od`)
  = [<c, (Stmt)`if <BExp b> then <Stmt s>; while <BExp b> do <Stmt s> od else skip fi`>];

CR rule("lookup", Ctx c, (AExp)`<Id x>`)
  = [<c, i>]
  when 
    isDefined(x, c.state), 
    Int i := lookup(x, c.state); 

  
CR rule("assign", Ctx c, (Stmt)`<Id x> := <Int i>`)
  = [<c[state=update(x, i, c.state)], (Stmt)`skip`>]
  when 
    isDefined(x, c.state);
  

rel[Conf,str,Conf] traceConf(Conf c) = traceGraph(#Conf, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 

void runConf(Conf c) = run(#Conf, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 

lrel[Conf,Conf] stepConf(Conf c) = step(#Conf, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 





