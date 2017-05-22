module paper::r5rs::Contexts


syntax E[&T]
  = F[("(" "handlers" Proc* EStar[&T] ")")]
  | F[("(" "dw" Id Expr EStar[&T] Expr ")")]
  | F[&T]
  ;


syntax EMulti[&T] = holeMulti: &T | E[&T];

syntax ESingle[&T] = holeSingle: &T | E[&T];
  
syntax F[&T]
  = hole: &T
  | "(" "if" FSingle[&T] Expr Expr ")"
  | "(" "set!" Id FSingle[&T] ")"
  | "(" "begin" FMulti[&T] Expr+ ")"
  //...
  ;
  
syntax FMulti[&T] = holeMulti: &T | F[&T];

syntax FSingle[&T] = holeSingle: &T | F[&T];
  
syntax PG[&T] = Store "|-" G[&T];
  

syntax G[&T]
  = F[("(" "dw" Id Expr G[&T] Expr ")")]
  | F[&T]
  ;

syntax H[&T]
  = F[("(" "handlers" Proc* H[&T] ")")]
  | F[Expr]
  ;   
  
  
//
//    (S hole (begin e e ... S es ...) (begin S es ...)
//       (begin0 e e ... S es ...) (begin0 S es ...)
//       (e ... S es ...) (if S es es) (if e S es) (if e e S)
//       (set! x S) (handlers s ... S es ... es) (handlers s ... S)
//       (throw x e) 
//       (lambda f S es ...) (lambda f e e ... S es ...)
//       (letrec ([x e] ... [x S] [x es] ...) es es ...)
//       (letrec ([x e] ...) S es ...)
//       (letrec ([x e] ...) e e ... S es ...)
//       (letrec* ([x e] ... [x S] [x es] ...) es es ...)
//       (letrec* ([x e] ...) S es ...)
//       (letrec* ([x e] ...) e e ... S es ...)))  
  

/*

(E (in-hole F (handlers proc ... E*)) (in-hole F (dw x e E* e)) F)
    (E* (hole multi) E)
    (Eo (hole single) E)
    
    (F hole (v ... Fo v ...) (if Fo e e) (set! x Fo)  
       (begin F* e e ...) (begin0 F* e e ...) 
       (begin0 (values v ...) F* e ...) (begin0 unspecified F* e ...)
       (call-with-values (lambda () F* e ...) v)
       (l! x Fo))
    
    (F* (hole multi) F)
    (Fo (hole single) F)
    
    ;; all of the one-layer contexts that "demand" their values, 
    ;; (maybe just "demand" it enough to ensure it is the right # of values)
    ;; which requires unspecified to blow up.
    (U (v ... hole v ...) (if hole e e) (set! x hole) (l! x hole)
       (call-with-values (lambda () hole) v))
    
    ;; everything except exception handler bodies
    (PG (store (sf ...) G))
    (G (in-hole F (dw x e G e))
       F)
    
    ;; everything except dw
    (H (in-hole F (handlers proc ... H)) F)
    
    (S hole (begin e e ... S es ...) (begin S es ...)
       (begin0 e e ... S es ...) (begin0 S es ...)
       (e ... S es ...) (if S es es) (if e S es) (if e e S)
       (set! x S) (handlers s ... S es ... es) (handlers s ... S)
       (throw x e) 
       (lambda f S es ...) (lambda f e e ... S es ...)
       (letrec ([x e] ... [x S] [x es] ...) es es ...)
       (letrec ([x e] ...) S es ...)
       (letrec ([x e] ...) e e ... S es ...)
       (letrec* ([x e] ... [x S] [x es] ...) es es ...)
       (letrec* ([x e] ...) S es ...)
       (letrec* ([x e] ...) e e ... S es ...)))
*/