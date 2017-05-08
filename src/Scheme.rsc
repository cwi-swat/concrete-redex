module Scheme

extend RRedex;
extend NameFix; 
import List;
import String;


layout Standard 
  = Whitespace* !>> [\t\n\ ];

lexical Whitespace
  = [\ \t\n];

syntax Expr
  = "(" Expr Expr* ")"
  | "(" "set!" Id Expr ")"
  | "(" "begin" Expr+ ")"
  | "(" "if" Expr Expr Expr ")"
  | Id \ "begin" \ "if"
  | Value
  ;

syntax Value
  = "(" "lambda" "(" Id* ")" Expr ")"
  | Num
  | "#t"
  | "#f"
  | "-" !>> [0-9]
  | "unspecified"
  ;
  
lexical Num
  = [\-]?[0-9]+ !>> [0-9]
  ;

lexical Id
  = ([a-zA-Z][0-9a-zA-Z_\-]* !>> [0-9a-zA-Z_\-]) \ "begin" \ "if" \ "-" \ "unspecified" \ "lambda"
  ;

syntax Store = "[" {VarValue ","}* "]";
syntax VarValue = Id "↦" Value;

syntax Conf = Store  "|-" Expr;

syntax P = Store "|-" E; 


syntax E 
  = hole: Expr //"[]"
  | "(" Expr* E Expr* ")"
  | "(" "set!" Id E ")"
  | "(" "begin" E Expr* ")"
  | "(" "if" E Expr Expr ")"
  ;

set[Tree] names((Expr)`(set! <Id x> <Expr _>)`) = {x};

set[Tree] names((Expr)`<Id x>`) = {x};

set[Tree] names((Expr)`(lambda (<Id* xs>) <Expr e>)`) = { x  | Id x <- xs };

set[Tree] names((Store)`[<{VarValue ","}* vs>]`)
  = { x | (VarValue)`<Id x> ↦ <Value v>` <- vs };

Tree prime(Id x) = [Id]"<x>_";

Refs resolve(Expr exp, Scope sc, Lookup lu) {
  top-down-break visit (exp) {
    case (Expr)`<Id x>`:
      return { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) };
  
    case (Expr)`(set! <Id x> <Expr e>)`: 
      return { <x@\loc, def, x> | loc def <- lu(x, x@\loc, sc) }
        + resolve(e, sc, lu);
        
    case t:(Expr)`(lambda (<Id* xs>) <Expr e>)`: 
      return { <x@\loc, x@\loc, x> | Id x <- xs } // defs refer to themselves
        + resolve(e, [ {<x, x@\loc, t@\loc> | Id x <- xs }, *sc], lu);
  }
  return {};
}

Tree subst(Expr e, Id x, Expr y) {
  return visit(e) {
    case (Expr)`<Id z>` => y
      when z == x
  }
}


//Tree subst(t:(Expr)`<Id y>`, Id x, Expr new) 
//  = new
//  when 
//    x == y;
//
//Tree subst(t:(Expr)`(lambda (<Id* xs>) <Expr e>)`, Id x, Expr new) 
//  = t
//  when
//    x <- xs;
//    
//Tree subst(t:(Expr)`(lambda (<Id* xs>) <Expr e>)`, Id x, Expr new) 
//  = (Expr)`(lambda (<Id* xs>) <Expr eNew>)`
//  when
//    !(x <- xs),
//    Expr eNew := subst(e, x, new);  
  
Conf paperExample() = (Conf)`[x ↦ 1] |- ((set! x (- x)) (set! x (- x)))`;    

Expr lambda() = (Expr)`(lambda (x) (set! x y))`;    

//CR rule("MApp", (P)`<Store s> |- <E c>`, (Expr)`((lambda (<Id* xs>) <Expr e>) <Expr* es>)`)
//  = <>
//  when
//    allValue(es);
  
CR rule("MSet", (P)`<Store s> |- <E e>`, (Expr)`(set! <Id x> <Value v>)`) = <(P)`<Store s2> |- <E e>`, (Expr)`unspecified`>
  when 
    isDefined(x, s),
    Store s2 := update(x, v, s);

CR rule("MLookup", (P)`<Store s> |- <E e>`, (Expr)`<Id x>`) = <(P)`<Store s> |- <E e>`, (Expr)`<Value v>`>
  when
    isDefined(x, s),
    Value v := lookup(x, s);

CR rule("MSeq", P p, (Expr)`(begin <Value v> <Expr e> <Expr* erest>)`) = <p, (Expr)`(begin <Expr e> <Expr* erest>)`>;

CR rule("MTrivSeq", P p, (Expr)`(begin <Expr e>)`) = <p, (Expr)`<Expr e>`>;

CR rule("MIfT", P p, (Expr)`(if <Value v> <Expr e1> <Expr e2>)`) = <p, e1>
  when (Value)`#f` !:= v;

CR rule("MIfF", P p, (Expr)`(if #f <Expr e1> <Expr e2>)`) = <p, e2>;

CR rule("MNeg", P p, (Expr)`(- <Num n>)`) = <p, [Expr]"<minN>">
  when
    int minN := -toInt("<n>");

bool isDefined(Id x, (Store)`[<{VarValue ","}* _>, <Id y> ↦ <Value _>, <{VarValue ","}* _>]`) = true
  when x == y;
 
default bool isDefined(Id x, Store _) = false; 
  
Value lookup(Id x, (Store)`[<{VarValue ","}* _>, <Id y> ↦ <Value v>, <{VarValue ","}* _>]`) = v
  when x == y;
  
Store update(Id x, Value v, (Store)`[<{VarValue ","}* v1>, <Id y> ↦ <Value _>, <{VarValue ","}* v2>]`)
  = (Store)`[<{VarValue ","}* v1>, <Id x> ↦ <Value v>, <{VarValue ","}* v2>]`
  when x == y;
 
bool allValue(Expr* es) = ( true | it && (Expr)`<Value v>` := e | Expr e <- es );
 

rel[Conf,str,Tree,Conf] traceScheme(Conf c) = traceGraph(#Conf, #P, c, 
  {"MSet", "MLookup", "MSeq", "MTrivSeq", "MNeg", "MIfT", "MIfF"}); 

void runScheme(Conf c) = run(#Conf, #P, c, {"MSet", "MLookup", "MSeq", "MTrivSeq", "MNeg", "MIfT", "MIfF"}); 



