module lang::credex::demo::r5rs::Arithmetic

import lang::credex::demo::rs5rs::Syntax;
import lang::credex::ParseRedex;
import lang::credex::demo::r5rs::Util;



CR red("5+0", P p, (Expr)`(#%+)`) = <p, (Expr)`0`>;

CR red("5+", P p, (Expr)`(#%+ <Expr+ es>)`) 
  = <p, [Expr]"<sum>">
  when 
    allNum(es),
    int sum := ( 0 | it + toInt(n) | (Expr)`<Num n>` <- es );


CR red("5u-", P p, (Expr)`(#%- <Num n1>)`) = <p, (Expr)`<Num n2>`>
  when n2 := [Num]"< -toInt(n1)>";
  
CR red("5-", P p, (Expr)`(#%+ <Num n1> <Expr+ es>)`) 
  = <p, [Expr]"<toInt(n1) - sum>">
  when 
    allNum(es),
    int sum := ( 0 | it + toInt(n) | (Expr)`<Num n>` <- es );
  
R red("5*1", P p, (Expr)`(#%*)`) = <p, (Expr)`1`>;

CR red("5*", P p, (Expr)`(#%+ <Expr+ es>)`) 
  = <p, [Expr]"<prod>">
  when 
    allNum(es),
    int prod := ( 1 | it * toInt(n) | (Expr)`<Num n>` <- es );
  
  
R red("5u/", P p, (Expr)`(#%/ <Num n1>)`) = <p, (Expr)`(#%/ 1 <Num n1>)`>;

CR red("5/", P p, (Expr)`(#%+ <Num n1> <Expr+ es>)`) 
  = <p, [Expr]"<toInt(n1) / prod>">
  when 
    allNum(es), ( true | it && (Expr)`0` !:= e | Expr e <- es ),
    int prod := ( 1 | it * toInt(n) | (Expr)`<Num n>` <- es );

  
set[str] arithmetic() = {"5+0", "5+", "5u-", "5-", "5*1", "5*", "5u/", "5/"};

