module lang::javascript::AbstractContexts

import lang::javascript::S5;
import credex::Matching;

import IO;


Expr example() = (Expr)`try break x 3 finally 5`;

void testNestedCtx() {
  t = (Expr)`try break x 3 finally 5`;
  splits = split(#E, t, #F, #G, #EPrime);
  
  println("******TERM = <t>");
  for (<ctx, redex> <- splits) {
    println("TOP ctx = <ctx2str(ctx)>");
    
    if (E e:/tryFinally(G g:/hole((Expr)`break <Id _> <Value _>`), Expr _) := ctx) {
      println("E-Finally-Break");
      println("e = <ctx2str(e)>");
      println("g = <ctx2str(g)>");
    }
  
  }
  
  t = (Expr)`try try break x 3 catch x 4 finally 5`;
  splits = split(#E, t, #F, #G, #EPrime);
  
  println("******TERM = <t>");
  for (<ctx, redex> <- splits) {
    println("TOP ctx = <ctx2str(ctx)>");
    
    if (E e:/tryFinally(G g:/hole((Expr)`break <Id _> <Value _>`), Expr _) := ctx) {
      println("E-Finally-Break");
      println("e = <ctx2str(e)>");
      println("g = <ctx2str(g)>");
    }
  
  }
  
   
}

/*
 * Contexts
 */
 
data EAE
  = class(EPrime eprime, Expr ext, Expr proto, Expr code, Expr primval) 
  | extensible(Expr class, EPrime eprime, Expr proto, Expr code, Expr primval)
  | proto(Expr class, Expr ext, EPrime eprime, Expr code, Expr primval)
  | code(Expr class, Expr ext, Expr proto, EPrime eprime, Expr primval)
  | primval(Expr class, Expr ext, Expr proto, Expr code, EPrime)
  ;
  
  
data EPE
  = config(EPrime eprime, Expr enum, Expr val, Expr writable)
  | enum(Expr config, EPrime eprime, Expr val, Expr writable)
  | \value(Expr config, Expr enum, EPrime eprime, Expr writable)
  | writable(Expr config, Expr enum, Expr val, EPrime eprime)
  
  | config2(EPrime eprime, Expr enum, Expr get, Expr \set)
  | enum2(Expr config, EPrime eprime, Expr get, Expr \set)
  | get(Expr config, Expr enum, EPrime eprime, Expr \set)
  | \set(Expr config, Expr enum, Expr get, EPrime)
  ;
  
data EPrime
  = hole(Expr expr)
  | op1(Op1 op1, EPrime)
  | op2(Op2 op2, EPrime eprime, Expr expr)
  | op2(Op2 op2, Value val, EPrime)
  | subO(EPrime eprime, O oo)
  | subOAssign(EPrime eprime, O oo, Expr expr)
  | subOAssign(Value val, O oo, EPrime)
  | subA(EPrime eprime, Expr expr, A a)
  | subAAssign(Value val, EPrime eprime, A a, Expr expr)
  | subAAssign(Value val, Value val, A a, EPrime)
  
  | subStar(EPrime eprime, Expr expr)  
  | subStar(Value val1, EPrime eprime)  
  | subStar(Value val1, Value val2)
  
  | delete(EPrime eprime, Expr expr)  
  | delete(Value val, EPrime eprime)  
    
  | subAssign(EPrime eprime, Expr expr, Expr expr)
  | subAssign(Value val1, EPrime eprime, Expr expr)
  | subAssign(Value val1, Value val2, EPrime eprim)
  | subAssign(Value val2, Value val2, Value val3)

  | call(EPrime eprime, list[Expr] args)
  | call(Value val, list[Value] vals, EPrime eprime, list[Expr] args)

  | assign(EPrime eprime, Expr expr)
  | assign(Value val, EPrime eprime)

  | \throw(EPrime eprime)
  | let(Id, EPrime eprime, Expr expr)

  | seq(EPrime eprime, Expr expr)
  | seq(Value val, EPrime eprime)
  | ifThenElse(EPrime eprime, Expr expr, Expr expr)
  | eval(EPrime eprime, Expr expr)
  | eval(Value val, EPrime eprime)
  | obj(AV av, list[StrPV] strpvs, Str string, EPE epe, list[StrPE] strpes)
  | props(EPrime eprime)
  ;
  
data E  
  = inject(EPrime eprime)
  | tryCatch(E e, Id x, Expr expr) 
  | tryFinally(E e, Expr expr) 
  | label(Id x, E e)
  | \break(Id x, E e)
  ;
  
  
// added to allow nested matching on G/F
data E
  = tryFinally(G g, Expr expr)
  | tryFinally(F f, Expr expr)
  | label(Id x, G g)
  | \break(Id x, G g)
  | inject(F f)
  ;
  
data F
  = inject(EPrime eprime)
  | label(Id, F)
  | \break(Id, F)
  ;
  
data G
  = inject(EPrime eprime)
  | tryCatch(G, Expr expr)
  ;