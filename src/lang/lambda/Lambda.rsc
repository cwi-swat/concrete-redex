module lang::lambda::Lambda

extend lang::std::Layout;
extend lang::std::Id;

/*
(define-language λv
  (e (e e ...) (if0 e e e) x v)
  (v (λ (x ...) e) number +)
  (E (v ... E e ...) (if0 E e e) hole)
  (x (variable-except λ + if0)))
*/
syntax Expr
  = Id \ "if0"
  | Value
  | "(" Expr+ ")"
  | "(" "if0" Expr Expr Expr ")"
  ; 

  
syntax Value
  = "(" "λ" "(" Id* ")" Expr ")"
  | Num
  | "+"
  ;


lexical Num
  = [0-9]+ !>> [0-9]; 