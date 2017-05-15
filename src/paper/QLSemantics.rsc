module paper::QLSemantics

extend paper::QL;
extend paper::Credex;
import IO;

/*

Questions re why semantics:

- read only from current state, or dynamically evolving state
   - only conditions/or compute questions?

- are invisible questions still accessible in computations?

- same questions rendered under different but not mut ex conditions?

- do we allow answerd questions to be come computed?

Accidental: normalize first?
how to represent visibility output?
flat list of dones? 

TODO: randomized inputs: analyze "done" form, as to what is enabled
then use gensen to synthesize random values. 

*/

syntax Store 
  = {IdValue ","}*
  ;
  
syntax Input = IdValue;

syntax IdValue = Id name "↦" Value val;

// extend stmt with done type
syntax Stm = done: Done;

syntax Done 
  = "computed" IdValue 
  | "widget" IdValue 
  | "done"; // for empty lists of statements.

syntax Conf = Store ";" IdValue "⊢" Form ;

syntax C 
  = Store store ";" IdValue input "⊢" F 
  ; 

syntax F = "form" Id S;

syntax Stm
  = Label Id ":" Type "=" Expr "[" Expr "]" 
  ;

syntax S
  = "if" "(" E ")" Stm !>> "else"
  | "if" "(" E ")" Stm "else" Stm
  | "if" "(" Value ")" S () !>> "else"
  | "if" "(" Value ")" S "else" Stm
  | "if" "(" Value ")" Done "else" S
  | "{" Stm* S Stm* "}" // variation point: pick any statement
  //"{" Done* S Stm!done* "}"
  | Label Id ":" Type "=" Expr "[" E "]"
  | hole: Stm!done 
  ;
  
// maintain two stores and do dirty-bit propagation
// input is in the second store. Final transition rewrites
// two store to new one.

syntax E
  = hole: Expr!val | bracket "(" E ")"
  | E "*" Expr | Value "*" E
  | E "/" Expr | Value "/" E
  | E "+" Expr | Value "+" E
  | E "-" Expr | Value "-" E
  | E "\>" Expr | Value "\>" E
  | E "\>=" Expr | Value "\>=" E
  | E "\<=" Expr | Value "\<=" E
  | E "\<" Expr | Value "\<" E
  | E "==" Expr | Value "==" E 
  | E "!=" Expr | Value "!=" E
  | E "&&" Expr // short-circuiting
  | E "||" Expr // short-circuiting 
  ;  
  
R reduceQL(Conf c) = reduce(#C, #Conf, red, c,  {"add", "sub", "mul", "div", "lookup",
  "leq", "geq", "gt", "lt", "eq", "neq", "and", "or", "not", 
  "ifThen", "ifThenElse", "question", "computed", "computedStart", "flatten"});
  
  
default CR red(str n, C c, Tree t)  // congruence
  = { <c, r> | Expr r <- red_e(n, t) }
  + { <c, r> | Stm r <- red_s(n, t) };

Conf example()
 = (Conf)`license ↦ true, age ↦ 19, num ↦ 10 ; age ↦ 20 ⊢ 
         'form Bla {
         '  "What is your name?" name: str
         '  "What is your age?" age: int
         '  if (age \> 18) {
         '    "Do you have a license?" license: bool
         '    "Computed age + num" comp: int = age + num
         '  }
         '  "What is your number?" num: int
         '}`;
 


/*
 * Statement reduction 
 */

default R red_s(str _, Tree _) = {};

R red_s("ifThen", (Stm)`if (<Bool v>) <Stm s>`)
  = {(Bool)`true` := v ? s : (Stm)`done`}; 

R red_s("ifThenElse", (Stm)`if (<Bool v>) <Stm s1> else <Stm s2>`)
  = {(Bool)`true` := v ? s1 : s2}; 

R red_s("computed", (Stm)`<Label l> <Id x>: <Type t> = <Expr e>`)
  = {(Stm)`<Label l> <Id x>: <Type t> = <Expr e> [<Expr e>]`};

//R red_s("flatten", (Stm)`{<Stm* s1> {<Stm* s2>} <Stm* s3>}`)
//  = {(Stm)`{<Stm* s1> <Stm* s2> <Stm* s3>}`}; 

CR red("question", C c, (Stm)`<Label l> <Id x>: <Type t>`)
  = {<c, (Stm)`<Label l> <Id x>: <Type t> = <Id x> [<Id x>]`>};


/*
 * Variable lookup
 */

// when in second store: dirty = false
CR red("lookup", C c, (Expr)`<Id x>`)
  = {<c, (Expr)`<Value v>`>}
  when isDefined(c.store, x),  Value v := lookup(c.store, x); 

/*
 * Basic expression reduction.
 *  Expr "[" Expr "]"
 */

default R red_e(str _, Tree _) = {};

//R red_e("value", (Expr)`<Value v>`)
//  = {(Expr)`<Value v>`}; 

R red_e("add", (Expr)`<Int i1> + <Int i2>`) 
  = {intExpr(toInt(i1) + toInt(i2))}; 

R red_e("sub", (Expr)`<Int i1> - <Int i2>`) 
  = {intExpr(toInt(i1) - toInt(i2))}; 

R red_e("mul", (Expr)`<Int i1> * <Int i2>`) 
  = {intExpr(toInt(i1) * toInt(i2))}; 

R red_e("div", (Expr)`<Int i1> / <Int i2>`) 
  = {intExpr(toInt(i1) / toInt(i2))}; 

R red_e("gt", (Expr)`<Int i1> \> <Int i2>`) 
  = {boolExpr(toInt(i1) > toInt(i2))}; 

R red_e("lt", (Expr)`<Int i1> \< <Int i2>`) 
  = {boolExpr(toInt(i1) < toInt(i2))}; 

R red_e("geq", (Expr)`<Int i1> \>= <Int i2>`) 
  = {boolExpr(toInt(i1) >= toInt(i2))}; 

R red_e("leq", (Expr)`<Int i1> \<= <Int i2>`) 
  = {boolExpr(toInt(i1) <= toInt(i2))}; 

R red_e("eq", (Expr)`<Value v1> == <Value v2>`) 
  = {boolExpr(v1 == v2)}; 

R red_e("neq", (Expr)`<Value v1> != <Value v2>`) 
  = {boolExpr(v1 != v2)}; 

R red_e("and", (Expr)`<Bool b> && <Expr e>`) 
  = {(Bool)`true` ? e : boolExpr(false)}; 

R red_e("or", (Expr)`<Bool b> || <Expr e>`) 
  = {(Bool)`false` ? e : boolExpr(true)}; 

R red_e("not", (Expr)`!<Bool b>`) 
  = {boolExpr(b != (Bool)`true`)}; 

/*
 * Helper functions
 */

int toInt(Int i) = toInt("<i>");

Expr intExpr(int n) = (Expr)`<Int i>` when Int i := [Int]"<n>";

Expr boolExpr(bool b) = b ? (Expr)`true` : (Expr)`false`;

bool isDefined((Store)`<{IdValue ","}* _>, <Id y> ↦ <Value v>, <{IdValue ","}* _>`, Id x) = true
  when x == y;

default bool isDefined(Store _, Id _) = false;

Value lookup((Store)`<{IdValue ","}* _>, <Id y> ↦ <Value v>, <{IdValue ","}* _>`, Id x) = v
  when x == y;
  
Store update((Store)`<{IdValue ","}* v1>, <Id y> ↦ <Value _>, <{IdValue ","}* v2>`, Id x, Value v)
  = (Store)`<{IdValue ","}* v1>, <Id x> ↦ <Value v>, <{IdValue ","}* v2>`
  when x == y;

default Store update((Store)`<{IdValue ","}* vs>`, Id x, Value v)
  = (Store)`<{IdValue ","}* vs>, <Id x> ↦ <Value v>`;
