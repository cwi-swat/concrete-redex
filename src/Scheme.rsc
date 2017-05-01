module Scheme

extend lang::std::Layout;
import RRedex;
import List;
import String;

syntax Expr
  = "(" Expr Expr* ")"
  | "(" "set!" Id Expr ")"
  | "(" "begin" Expr+ ")"
  | "(" "if" Expr Expr Expr ")"
  | Id \ "begin" \ "if"
  | Value
  ;

syntax Value
  = "(" "lambda" "(" Id+ ")" Expr ")"
  | Num
  | "#t"
  | "#f"
  | "-"
  | "unspecified"
  ;
  
lexical Num
  = [0-9]+ !>> [0-9]
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
  | "(" Value* E Expr* ")"
  
  /*
   "(" E Expr* ")"
   "(" Value E Expr* ")"
   "(" Value Value E Expr* ")"
  */
  
  
  | "(" "set!" Id E ")"
  | "(" "begin" E Expr* ")"
  | "(" "if" E Expr Expr ")"
  ;
  
//CR rule("MApp", (P)`<Store s> |- <E c>`, (Expr)`((lambda (<Id+ xs>) <Expr e>) <Expr* args>)`)
//  = <(P)`<Store s2> |- <E c>`, e2>
//  when 
//    allValue(args),
//    list := fresh(xs, s),
//    Expr e2 := subst(xs, ys, e),
//    Store s2 := updateMany([ x | Id x <- xs], [ v | Value x <- args ], s); 
     
  
CR rule("MSet", (P)`<Store s> |- <E e>`, (Expr)`(set! <Id x> <Value v>)`)
  = <(P)`<Store s2> |- <E e>`, (Expr)`unspecified`>
  when 
    isDefined(x, s),
    Store s2 := update(x, v, s);

CR rule("MLookup", (P)`<Store s> |- <E e>`, (Expr)`<Id x>`)
  = <(P)`<Store s> |- <E e>`, (Expr)`<Value v>`>
  when
    isDefined(x, s),
    Value v := lookup(x, s);

CR rule("MSeq", P p, (Expr)`(begin <Value v> <Expr e> <Expr* erest>)`)
  = <p, (Expr)`(begin <Expr e> <Expr* erest>)`>;

CR rule("MTrivSeq", P p, (Expr)`(begin <Expr e>)`)
  = <p, (Expr)`<Expr e>`>;

CR rule("MIfT", P p, (Expr)`(if <Value v> <Expr e1> <Expr e2>)`)
  = <p, e1>
  when (Value)`#f` !:= v;

CR rule("MIfF", P p, (Expr)`(if #f <Expr e1> <Expr e2>)`)
  = <p, e2>;

CR rule("MNeg", P p, (Expr)`(- <Num n>)`)
  = <p, minN>
  when
    Expr minN := [Expr]"< -toInt("<n>")>";

bool isDefined(Id x, (Store)`[<{VarValue ","}* _>, <Id y> ↦ <Value _>, <{VarValue ","}* _>]`)
  = true
  when x == y;
  
Value lookup(Id x, (Store)`[<{VarValue ","}* _>, <Id y> ↦ <Value v>, <{VarValue ","}* _>]`)
  = v
  when x == y;
  
Store update(Id x, Value v, (Store)`[<{VarValue ","}* v1>, <Id y> ↦ <Value _>, <{VarValue ","}* v2>]`)
  = (Store)`[<{VarValue ","}* v1>, <Id x> ↦ <Value v>, <{VarValue ","}* v2>]`
  when x == y;
 
bool allValue(Expr* es) = ( true | it && (Expr)`<Value v>` := e | Expr e <- es );
 



