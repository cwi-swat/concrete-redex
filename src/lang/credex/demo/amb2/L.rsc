module lang::credex::demo::amb2::L


data Expr
  = app(Expr l, Expr r)
  | abs(str x, Type t, Expr e)
  | var(str x)
  | amb(list[Expr] es)
  | add(list[Expr] es)
  | if0(Expr c, Expr e1, Expr e2)
  | fix(Expr e)
  ;
  
data Type
  = func(Type t1, Type t2)
  | \num()
  ;
  
data Prog
  = prog(list[Expr] es);
  
data P
  = prog(list[Expr] es1, E e, list[Expr] es2)
  ;
  
data E
  = app(Value v, E e)
  | app(E e, Expr exp)
  | add(list[Value] vs, E e, list[Expr] es)
  | if0(E e, Expr e1, Expr e2)
  | fix(E e)
  | hole()
  ;
  
data Value
  = abs(str x, Type t, Expr e)
  | fix(Value v)
  | \num(num n)
  ;
  
  
void red("if0t", P p, if0(\num(0), Expr e2, Expr e2)) = inHole(p, e1);

void red("if0f", P p, if0(!\num(0), Expr e2, Expr e2)) = inHole(p, e2);

void red("fix", P p, app(fix(abs(str x, Type t, Expr e1)), Expr e2));





