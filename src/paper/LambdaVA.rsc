module paper::LambdaVA

import paper::Lambda;
import paper::LambdaResolve;
import credex::Matching;
import Type;
import ParseTree;
import String;


alias CR = rel[node, Tree];
alias R = set[Tree];

data E // evaluation contexts
  = apply(list[Value] done, E ctx, list[Expr] rest)
  | hole(Expr redex)
  ;
  
  
CR red("+", E e:/hole((Expr)`(+ <Num n1> <Num n2>)`))
  = {<e, [Expr]"<toInt(n1) + toInt(n2)>">};

CR red("βv", E e:/hole((Expr)`((λ (<Id x>) <Expr b>) <Value v>)`))
  = {<e, subst((Expr)`<Id x>`, (Expr)`<Value v>`, b)>};

default CR red(str _, E _) = {};

R reduceLambdaVA(Expr e) = reduce(#E, #Expr, red, e, {"+", "βv"});

// NB: trace/steps/etc. are still reusable with abstract context matching.
R reduce(type[&C<:node] ct, type[&T<:Tree] tt, CR(str,&C) red, &T t, set[str] rules)
  = { typeCast(#Tree, plug(tt, ctx2, t, rt)) |  ctx1 <- split(ct, t), 
        str r <- rules, <ctx2, rt> <- red(r, ctx1) };

private int toInt(Num x) = toInt("<x>");  
  
Expr omega() = (Expr)`((λ (x) (x x)) (λ (x) (x x)))`;
Expr onePlusOne() = (Expr)`(+ 1 1)`;
Expr onePlusTwo() = (Expr)`((λ (x) (+ x 2)) 1)`;

Expr avoidCapture() 
 = (Expr)`((λ (x) ((λ (y) (+ y x)) x)) (λ (z) y))`;

