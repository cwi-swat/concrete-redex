module lang::credex::demo::imp2::Semantics

import lang::credex::demo::imp2::Contexts;
import lang::credex::demo::imp2::State;

extend lang::credex::ParseRedex;
import String;


default CR red(str _, C _, Tree _) = {};

CR red("var", C c, (E)`<Id x>`) = {<c, (Expr)`<Int i>`>}
  when Int i := lookup(x, c.state); 


CR red("+", C c, (E)`<Int i1> + <Int i2>`) = {<c, (Expr)`<Int i>`>} 
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 + n2>";

CR red("/", C c, (E)`<Int i1> / <Int i2>`) = {<c, (Expr)`<Int i>`>}
  when
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Int i := [Int]"<n1 / n2>";


CR red("≤", C c, (E)`<Int i1> \<= <Int i2>`) = {<c, (Expr)`<Bool b>`>}
  when 
    int n1 := toInt("<i1>"),
    int n2 := toInt("<i2>"),
    Bool b := [Bool]"<n1 <= n2>";

CR red("not", C c, (E)`not <Bool b>`) = {<c, isTrue(b) ? (Expr)`false` : (Expr)`true`>};
  
CR red("and", C c, (E)`<Bool b> and <Expr e>`) = {<c, isTrue(b) ? e : (Expr)`false`>};

CR red(":=", C c, (S)`<Id x> := <Int i>`) 
  = {<c[state=update(x, i, c.state)], (Stmt)`skip`>};

CR red("seq1", C c, (S)`skip; <Stmt s1>`) = {<c, s1>};

CR red("seq2", C c, (S)`skip; <Stmt s1>; <{Stmt ";"}+ s2>`) 
  = {<c, (Stmt)`<Stmt s1>; <{Stmt ";"}+ s2>`>};

CR red("if", C c, (S)`if <Bool b> then <Stmt s1> else <Stmt s2> fi`) 
  = {<c, isTrue(n) ? s1 : s2>};

CR red("while", C c, (S)`while <Expr b> do <Stmt s> od`)
  = {<c, (Stmt)`if <Expr b> then <Stmt s>; while <Expr b> do <Stmt s> od else skip fi`>};


bool isTrue(Bool b) = (Bool)`true` := b;
