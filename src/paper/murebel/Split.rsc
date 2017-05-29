module paper::murebel::Split

import paper::murebel::Aux;
import ParseTree;
import IO;
import Type;

extend paper::TraceRedex;

/*
 * This approach doesn't work because plug can't be made reliable.
 * creating plug data during split, will make it not nice to write
 * `hole` definitions.
 */ 

alias CR = rel[Tree context, Tree reduct]; // context reduct pairs

RR apply(type[&T<:Tree] tt, CR(str, &T, Tree) red, &T t, set[str] rules)
  = { <r, plug(ctx2, rt, rx@\loc)> |
    bprintln("STARTING REDUCTION"),  
    Tree rx <- hole(t),
    bprintln("REDEX: <rx>"),
     str r <- rules,
     <&T ctx2, Tree rt> <- red(r, t, rx)
     , bprintln("<rx> === <r> ===\> <rt>")
      };

Tree plug(Tree ctx, Tree reduct, loc l) {
  int found = 0;
  bool yes(Tree t) {
    println("Replaced <t> with <reduct>");
    found += 1;
    return true;
  }
  newT =  visit (ctx) {
    case Tree t => reduct[@\loc=t@\loc]
      when typeOf(t) == typeOf(reduct), t@\loc?, t@\loc == l, yes(t)
  }
  assert found > 0: "not plugged <reduct> back into <ctx>";
  assert found == 1: "multiple plugs for <reduct>";
  return newT;
}


list[Tree] stack = [];
rel[Tree(Tree), Tree] hole2(Tree t) {
  parent = stack[-1];
  // find t in parent (?) and make plug
  // push t on stack and call hole
}

bool terminated(Stmt s) = s is skip || s is \fail;

bool allTerminated(Stmt* ss) = ( true | it && terminated(s) | Stmt s <- ss );

bool isValue(Expr e) = (Expr)`<Value _>` := e;

bool allValue({Expr ","}* es) = ( true | it && isValue(e) | Expr e <- es );

default set[Tree] hole(Tree t) = {t};

set[Tree] hole((Conf)`<Store _>, <Locks _> ⊢ <Stmt* ss> <Stmt s> <Stmt* _>`) = hole(s)
  when allTerminated(ss), !terminated(s);

set[Tree] hole(x:(Stmt)`{<Stmt* ss> <Stmt s> <Stmt* _>}`) = hole(s)
  when allTerminated(ss), !terminated(s);
  
set[Tree] hole((Stmt)`<Expr e>.<Id _> = <Expr _>;`) = hole(e)
  when !isValue(e);
  
set[Tree] hole((Stmt)`<Value _>.<Id _> = <Expr e>;`) = hole(e)
  when !isValue(e);

set[Tree] hole((Stmt)`par <Stmt s>`) = hole(s)
  when !(s is block), !terminated(s);

set[Tree] hole((Stmt)`par {<Stmt* ss>}`) 
  = { *hole(s) | Stmt s <- ss, !terminated(s) }
  when Stmt s <- ss, !terminated(s); // when there's at least one
  
set[Tree] hole((Stmt)`sync (<{LId ","}* _>) <Stmt s>`) = hole(s)
  when !terminated(s);

set[Tree] hole((Stmt)`onSuccess (<Ref _> ↦ <Id _>) <Stmt s>`) = hole(s)
  when !terminated(s);

set[Tree] hole((Stmt)`let <Id _> = <Expr e> in <Stmt _>`) = hole(e)
  when !isValue(e);
  
set[Tree] hole((Stmt)`if (<Expr e>) <Stmt _>`) = hole(e)
  when !isValue(e);

set[Tree] hole((Stmt)`if (<Expr e>) <Stmt _> else <Stmt _>`) = hole(e)
  when !isValue(e);
  
set[Tree] hole((Stmt)`<Expr e>.<Id _>(<{Expr ","}* _>);`) = hole(e)
  when !isValue(e);

set[Tree] hole((Stmt)`<Value _>.<Id _>(<{Expr ","}* es>, <Expr e>, <{Expr ","}* _>);`) = hole(e)
  when allValue(es), !isValue(e);

set[Tree] hole((Expr)`<Expr e>.<Id _>`) = hole(e) when !isValue(e);

set[Tree] hole((Expr)`!<Expr e>`) = hole(e) when !isValue(e);

set[Tree] hole((Expr)`<Expr e> in <Id _>`) = hole(e) when !isValue(e);

set[Tree] hole((Expr)`(<Expr e>)`) = hole(e) when !isValue(e);

set[Tree] hole((Expr)`<Expr e> + <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> + <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> - <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> - <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> * <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> * <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> / <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> / <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> \> <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> \> <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> \>= <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> \>= <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> \< <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> \< <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> \<= <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> \<= <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> == <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> == <Expr e>`) = hole(e);

set[Tree] hole((Expr)`<Expr e> != <Expr _>`) = hole(e) when !isValue(e);
set[Tree] hole((Expr)`<Value _> != <Expr e>`) = hole(e);



