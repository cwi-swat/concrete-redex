module paper::effects::Choose

extend paper::effects::Semantics;
extend paper::effects::Syntax;
extend paper::ParseRedex;
import Boolean;
import String;
import util::Math;

syntax Value
  = left Value "-" Value
  | "max_" Value
  ;
  
syntax E
  = "return" V
  | Op "(" V ";" Id "." Computation ")"
  | Op V 
  | "if" V "then" Computation "else" Computation
  | V Value
  | Value V
  | "with" V "handle" Computation 
  ;
  
syntax V
  = hole: Value
  | V "-" Value
  | Num "-" V
  | "(" V "," Value ")"
  | "(" Num "," V ")"
  | "(" V ")"
  | "max_" V
  ;


CR red("bracket", E e, (Value)`(<Num x>)`)
  = {<e, (Value)`<Num x>`>};

CR red("minus", E e, (Value)`<Num x> - <Num y>`)
  = {<e, (Value)`<Num n>`>}
  when 
    Num n := [Num]"<toInt(x) - toInt(y)>";

CR red("max", E e, (Value)`max_ (<Num x>, <Num y>)`)
  = {<e, (Value)`<Num n>`>}
  when 
    Num n := [Num]"<max(toInt(x), toInt(y))>";
    

int toInt(Num n) = toInt("<n>");

CR red("decide", E e, (Computation)`decide_ <Value _>`)
  = {<e, (Computation)`return <Value v>`>}
  when Value v := [Value]"<arbBool()>";

RR applyChoose(Computation c) = apply(#E, #Computation, red, c, 
   effReductions() + {"decide", "minus", "max", "bracket"});  


Computation example1() = (Computation)`do choose ⟵ return <Value ch> in with <Value pt> handle <Computation cd>`
  when
    Value ch := choose(),
    Value pt := pickTrue(),
    Computation cd := chooseDiff();

Computation example2() = (Computation)
  `do choose ⟵ return <Value ch> in
  'do max ⟵ return <Value mx> in
  'with <Value pm> handle <Computation cd>`
  when
    Value mx := maxFun(),   
    Value ch := choose(),
    Value pm := pickMax(),
    Computation cd := chooseDiff();

Value maxFun() = (Value)
  `fun (x,y) ↦ return max_ (x, y)`;

Value choose() = (Value)
  `fun (x,y) ↦ do b ⟵ decide! () in if b then return x else return y`;
  
Value pickTrue() = (Value)
  `handler { return x ↦ return x, decide!(_; k) ↦ k true }`;
  
Value pickMax() = (Value)
  `handler { return x ↦ return x, 
  '  decide!(_; k) ↦ 
  '    do xt ⟵ k true in
  '    do xf ⟵ k false in
  '    do mx ⟵ max (xt, xf) in
  '    return mx
  '}`;
  
Computation chooseDiff() = (Computation)
  `do x1 ⟵ choose (15, 30) in
  'do x2 ⟵ choose (5, 10) in
  'return (x1 - x2)`;
