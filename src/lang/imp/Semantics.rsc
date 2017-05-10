module lang::imp::Semantics

extend lang::imp::IMP;
extend credex::ConcreteRedex;

import String;

syntax AE
  = AE "+" AExp
  | AExp "+" AE
  | AE "/" AExp
  | AExp "/" AE
  | hole: AExp //"☐"
  ;

syntax BE
  = AE "\<=" AExp
  | Int "\<=" AE 
  | "not" BE
  | BE "and" BExp
  | hole: BExp //"☐"
  ;

syntax S
  = Id ":=" AE
  | S ";" Stmt
  | "if" BE "then" Stmt "else" Stmt "fi"
  | hole: Stmt //"☐"
  ;
  
syntax C
  = State "⊢" S
  ;

syntax State
  = "[" {VarInt ","}* "]";

syntax VarInt
  = Id "↦" Int
  ;

syntax Conf
  = State "⊢" Stmt
  ;
  
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

CR rule("lookup", c:(C)`<State s> ⊢ <S _>`, (AExp)`<Id x>`)
  = <c, (AExp)`<Int i>`>
  when 
    isDefined(x, s), 
    Int i := lookup(x, s); 


CR rule("add", C c, (AExp)`<Int i1> + <Int i2>`) = <c, (AExp)`<Int i>`> 
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 + n2>";

CR rule("div", C c, (AExp)`<Int i1> / <Int i2>`) = <c, (AExp)`<Int i>`>
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 / n2>";


CR rule("leq", C c, (BExp)`<Int i1> \<= <Int i2>`) = <c, b ? (BExp)`true` : (BExp)`false`>
  when 
    bool b := toInt("<i1>") <= toInt("<i2>");

CR rule("not-false", C c, (BExp)`not false`) = <c, (BExp)`true`>;

CR rule("not-true", C c, (BExp)`not true`) = <c, (BExp)`false`>;
  
CR rule("and-true", C c, (BExp)`true and <BExp b>`) = <c, b>;

CR rule("and-false", C c, (BExp)`false and <BExp b>`) = <c, (BExp)`false`>;

CR rule("seq", C c, (Stmt)`skip; <Stmt s2>`) = <c, s2>;

CR rule("if-true", C c, (Stmt)`if true then <Stmt s1> else <Stmt s2> fi`) = <c, s1>;

CR rule("if-false", C c, (Stmt)`if false then <Stmt s1> else <Stmt s2> fi`) = <c, s2>;

CR rule("while", C c, (Stmt)`while <BExp b> do <Stmt s> od`)
  = <c, (Stmt)`if <BExp b> then <Stmt s>; while <BExp b> do <Stmt s> od else skip fi`>;

CR rule("assign", (C)`<State s> ⊢ <S c>`, (Stmt)`<Id x> := <Int i>`) = <(C)`<State s2> ⊢ <S c>`, (Stmt)`skip`>
  when 
    isDefined(x, s), 
    State s2 := update(x, i, s);

rel[Conf,str,Tree,Conf] traceConf(Conf c) = traceGraph(#Conf, #C, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 
 
void runConf(Conf c) = run(#Conf, #C, c, {"leq", "seq", "if-true",
  "if-false", "lookup", "assign", "add", "div", "while", "not-false",
  "not-true", "and-true", "and-false"}); 


bool isDefined(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = true
  when x == y;
  
Int lookup(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`)
  = i
  when x == y;
  
State update(Id x, Int i, (State)`[<{VarInt ","}* v1>, <Id y> ↦ <Int _>, <{VarInt ","}* v2>]`)
  = (State)`[<{VarInt ","}* v1>, <Id x> ↦ <Int i>, <{VarInt ","}* v2>]`
  when x == y;

