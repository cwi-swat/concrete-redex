module paper::r5rs::Syntax

syntax Prog
  = Store "⊢" DWS* Def*;

syntax Store
  = {SF ","}* entries;
  
syntax Key
  = pp: "." Num n
  | cp: "λ" Num n
  | mp: "μ" Num n
  | id: Id id 
  ;
  
syntax Stored
  = val: Value
  | cons: "(" "#%cons" Value Value ")" 
  | lambda: "(" "lambda" "(" Id* ")" Expr+ ")" 
  | lambdaDot: "(" "lambda" "(" Id* "." Id ")" Expr+ ")"
  | lambdaAll: "(" "lambda" Id Expr+ ")"
  ;
  
syntax SF 
  = val: Key!pp!cp!mp key "↦" Stored!cons!lambda!lambdaDot!lambdaAll 
  | pair: Key!cp!mp!id key "↦" Stored!val!lambda!lambdaDot!lambdaAll
  | closure: Key!mp!pp!id key "↦" Stored!cons!val!lambdaDot!lambdaAll
  | manyClosure: Key!pp!cp!id key "↦" Stored!cons!val!lambda 
  ;
  
syntax DWS = "(" Id "(" Value ")" "(" Value ")" ")";

syntax Def 
  = "(" "define" Id Expr ")"
  | "(" "begin^D" Def* ")"
  | Expr
  ;
  
syntax Expr
  = "(" Expr+ ")"
  | "(" Expr* Expr "⬦" Expr* ")"
  | "(" "if" Expr Expr Expr ")"
  | "(" "if" Expr Expr ")"
  | "(" "set!" Id Expr ")"
  | "(" "begin" Expr+ ")"
  | Id
  | Value
  | "(" "push" Dws ")"
  | "(" "pop" ")"
  | "(" "throw" Id Dws* D /* D[x] ??? */ ")"
  | "(" "lambda" "(" Id* ")" Expr+ ")" // should Expr*??? or Id+?
  | "(" "lambda" "(" Id+   "." Id ")" Expr+ ")"
  | "(" "lambda" Id Expr+ ")"
  ;
  
syntax Value = NonFun | Fun;

syntax NonFun
  = PP
  | "#%null"
  | "\'" Sym
  | SQV
  | "unspecified"
  ;
  
syntax Fun
  = UFun 
  | AOp
  | Fun1
  | Fun2
  | "#%list"
  | "#%dynamic-wind"
  | "#%apply"
  | "#%values"
  ;

syntax Fun1
  = "#%null?"  
  | "#%pair?"  
  | "#%car"  
  | "#%cdr"  
  | "#%call/cc"  
  | "#%eval"
  ;
  
syntax Fun2  
  = "#%cons"  
  | "#%set-car!"  
  | "#%set-cdr!"  
  | "#%eqv?"  
  | "#%call-with-values" 
  ;

syntax UFun  
  = CP | MP;
  
syntax AOp
  = "#%+"
  | "#%-"
  | "#%/"
  | "#%*"
  ;
   
syntax P = Store "⊢" W;
syntax W = Dws* D Def*;

syntax D
 = EMany
 | "(" "define" Id EOne ")"
 ;

syntax E
  = hole: Expr
  | "(" Expr* EOne "⬦" Expr* ")"
  | "(" "if" EOne Expr Expr ")"
  | "(" "if" EOne Expr ")"
  | "(" "set!" Id EOne ")"
  | "(" "begin" EMany Expr+ ")"
  | "(" "#%call-with-values" "(" "lambda" "(" ")" EMany Expr* ")" Value ")"
  ;

// these holes need to be named
// so the redex needs to have some kind of tag so we can check it in the rules.
syntax EOne = \hole-single: Expr | E; 

syntax EMany = \hole-multi: Expr | E;

syntax DS
  = ES | "(" "define" Id ES ")" | "(" "begin^D" DS* ")";

syntax ES
  = "\'" Synt
  | "(" "ccons" ES ES ")"
  | "(" ES+ ")"
  | "(" ES* ES "⬦" ES* ")"
  | "(" "if" ES ES ES ")"
  | "(" "if" ES ES ")"
  | "(" "set!" Id ES ")"
  | "(" "begin" ES+ ")"
  | Id
  | Value
  | "(" "push" DWS ")"
  | "(" "pop" ")"
  | "(" "throw" Id DWS* D ")" // D[x] ???
  | "(" "lambda" "(" Id* ")" ES+ ")"
  | "(" "lambda" "(" Id+ "." Id ")" ES+ ")"
  | "(" "lambda" Id ES+ ")"
  ;
  
syntax Syn
  = "(" Syn* ")"
  | "(" Syn+ "." SQV ")"
  | "(" Syn+ "." Sym ")"
  | SQV
  | Sym
  ;
  
syntax SQV
  = Num 
  | "#t"
  | "#f"
  ;
  
syntax SP
  = Store "⊢" DWS* Def* SD Syn*
  ;
  
syntax SD
  = S
  | "(" "define" Id S ")"
  | "(" "begin^D" Def* SD Syn* ")"
  ;

syntax S
  = hole: Expr
  | "(" Expr* S Syn* ")"
  | "(" "if" Expr Expr S ")"
  | "(" "if" Expr S Syn ")"
  | "(" "if" S Syn Syn ")"
  | "(" "if" Expr S ")"
  | "(" "if" S Syn ")"
  | "(" "set!" Id S ")"
  | "(" "begin" Expr+ S Syn* ")"
  | "(" "begin" S Syn* ")"
  | "(" "throw" Id DWS* S ")"
  | "(" "push" "(" Id Expr S ")" ")"
  | "(" "push" "(" Id S Syn ")" ")"
  | "(" "lambda" "(" Id* ")" S Syn* ")"
  | "(" "lambda" "(" Id* ")" Expr+ S Syn* ")"
  | "(" "lambda" "(" Id+ "." Id ")" S Syn* ")"
  | "(" "lambda" "(" Id+ "." Id ")" Expr+ S Syn* ")"
  | "(" "lambda" Id S Syn* ")"
  | "(" "lambda" Id Expr+ S Syn* ")"
  | "(" "ccons" Value S ")"
  | "(" "ccons" S Syn ")"
  | S "⬦"
  ;
 
keyword Keywords
  = "lambda" | "ccons" | "push" | "begin" | "throw"
  | "if" | "define" | "unspecified"; 
 
syntax Sym
  = ID \ ".";
  
syntax Id
  = ID \  Keywords;

syntax Num
  = [0] !>> [0-9]
  | [1-9][0-9]* !>> [0-9]
  ;



