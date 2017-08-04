module lang::javascript::Semantics

import lang::javascript::Contexts;



// E-Compat
R red(str n, c:(C)`<Store s> <Heap h>; <E _>`, Expr e)
  = // E-Compat
    { <c, r> | Expr r <- redE(n, e) }
  // E-EnvStore
  + { <c[store=s2], r> | <Store s2, Expr r> <- redEs(n, s, e) }
  // E-Objects
  + { <c[heap=h2], r> | <Heap h2, Expr r> <- redEh(n, h, e) }
  // E-Control
  + { <c, r> | Expr r <- redECtrl(n, e) }
  // E-Eval
  // todo
  ;

CR redECtrl("E-Finally-Error", E c:/(E)`try <F f> finally <Expr e>`, r:(Expr)`err <Value v>`)
  = {<c, (Expr)`<Expr e>; err <Value v>`>} 
  when inHole(f, r); // is inHole needed? Or does it follow that redex is in f,
    // because well-formedness of context grammar? Context sorts go to hole, always?


CR redECtrl("E-Uncaught", c:(E)`<F f>`, r:(Expr)`err <Value v>`)
  = {<c, (Expr)`err <Value v>`>};


CR redECtrl("E-Uncaught", E e:inject(F f:/hole((Expr)`err <Value v>`)))
  = {<e, (Expr)`err <Value v>`>};  

CR redECtrl("E-Finally-Error", E c:/(Expr)`try <F f> finally <Expr e>`)
  = redECtrlF(c, f, getHole(f));
  
CR redECtrlF(E c, F f, (Expr)`err <Value v>`)
  = {<c, (Expr)`<Expr e>; err <Value v>`>};


  
