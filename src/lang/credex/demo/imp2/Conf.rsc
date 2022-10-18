module lang::credex::demo::imp2::Conf

extend lang::credex::demo::imp2::Syntax;

syntax Conf = State "⊢" Stmt;

syntax State = "[" {VarInt ","}* "]";

syntax VarInt = Id "↦" Int;

Int lookup(Id x, (State)`[<{VarInt ","}* _>, <Id y> ↦ <Int i>, <{VarInt ","}* _>]`) = i
  when x == y;
  
State update(Id x, Int i, (State)`[<{VarInt ","}* v1>, <Id y> ↦ <Int _>, <{VarInt ","}* v2>]`)
  = (State)`[<{VarInt ","}* v1>, <Id x> ↦ <Int i>, <{VarInt ","}* v2>]`
  when x == y;
