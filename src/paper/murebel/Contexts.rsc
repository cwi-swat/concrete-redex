module paper::murebel::Contexts

extend paper::murebel::Syntax;
import List;
import String;

syntax Obj = Ref ref ":" Id class "[" St state "]"  "{" {Prop ","}* props "}" ;

syntax St = "⊥" | Id;

syntax Value = Ref;

syntax Ref = "#" Num ptr;  

syntax Prop = Id name ":" Value val;

syntax Store = Obj* objs;

syntax Lock = LId id "{" Obj* reads "|" Obj* writes "}";
  
syntax LId = "@" Num id;  
  
syntax Conf = Store store "," Locks locks "⊢" Stmt*;
  
syntax Locks = Lock* locks;
  
syntax C = Store store "," Locks locks "⊢" S stmt Stmt*;

syntax Refs = Ref* refs;

syntax Stmt  
  = "onSuccess" "(" Ref "↦" Id ")" Stmt 
  | "sync" "(" {LId ","}* locks ")" Stmt
  ;

syntax S
  = hole: Stmt!skip!fail // this one makes it always ambiguous...
  // using the following approach we might reduce ambiguity
  // but it means matching redexes on S, not Stmt
  //= hole: "{" ";" Stmt* "}"
  //| hole: "{" "}"
  //| hole: "{" "fail" ";" Stmt* "}"
  //| hole: Ref "." Id "=" Value ";"
  //| hole: "par" ";"
  //| hole: "par" "fail" ";"
  //| hole: "onSuccess" "(" Ref "↦" Id ")" ";"
  //| hole: "onSuccess" "(" Ref "↦" Id ")" "fail" ";"
  //| hole: "sync" Stmt
  //| hole: "let" Id "=" Value "in" Stmt
  //| hole: Value "." Id "(" {Value ","}* ")" ";"
  //| hole: "if" "(" Value ")" Stmt () !>> "else" 
  //| hole: "if" "(" Value ")" Stmt "else" Stmt 
  //| hole: Value "." Id "(" {Value ","}+  ")" ";"
  
  | block: "{" S Stmt* "}"
  | E "." Id "=" Expr ";"
  | Value "." Id "=" E ";"
  | "par" S!block
  | "par" "{" Stmt* S Stmt* "}" // NB: only parallelism at par level, not below it. 
  // NB * not + because of concrete syntax bug
  | "sync" "(" {LId ","}* ")" S // NB: don't go into sync S 
  | "onSuccess" "(" Ref "↦" Id ")" S
  | "let" Id "=" E "in" Stmt
  | "if" "(" E ")" Stmt () !>> "else" 
  | "if" "(" E ")" Stmt "else" Stmt 
  | E "." Id "(" {Expr ","}* ")" ";"
  | Value "." Id "(" E ")" ";"
  | Value "." Id "(" E "," {Expr ","}+ ")" ";"
  | Value "." Id "(" {Value ","}+ "," E "," {Expr ","}+ ")" ";"
  | Value "." Id "(" {Value ","}+ "," E ")" ";"
  ;

syntax E
  = hole: Expr!value
  | E "." Id
  | E "*" Expr
  | Value "*" E
  | E "/" Expr
  | Value "/" E
  | E "-" Expr
  | Value "-" E
  | E "+" Expr
  | Value "+" E
  | E "\>" Expr
  | Value "\>" E
  | E "\>=" Expr 
  | Value "\>=" E 
  | E "\<" Expr 
  | Value "\<" E 
  | E "\<=" Expr 
  | Value "\<=" E 
  | E "==" Expr 
  | Value "==" E 
  | E "!=" Expr
  | Value "!=" E
  ; 


int arity({Expr ","}* es) = size([ e | Expr e <- es ]);
int arity({Formal ","}* fs) = size([ f | Formal f <- fs ]);

// NB: if in init state, the transition *must* have a to-state
Trans normalize((Trans)`on <Id x> (<{Formal ","}* fs>) <Stmt s>`, (St)`<Id state>`)
  = (Trans)`on <Id x> (<{Formal ","}* fs>) : <Id state> require true <Stmt s>`;   

Trans normalize((Trans)`on <Id x> (<{Formal ","}* fs>) <Goto g> <Stmt s>`, St _)
  = (Trans)`on <Id x> (<{Formal ","}* fs>) <Goto g> require true <Stmt s>`;   

Trans normalize((Trans)`on <Id x> (<{Formal ","}* fs>) <Pre pre> <Stmt s>`, (St)`<Id state>`)
  = (Trans)`on <Id x> (<{Formal ","}* fs>) : <Id state> <Pre pre> <Stmt s>`;

default Trans normalize(Trans t, St _) = t;   
 
bool allValue({Expr ","}* exprs)
  = ( true | it && (Expr)`<Value _>` := e | e <- exprs );

LId newLock(Locks locks) = (LId)`@<Num id>`
  when 
    list[int] ns := [ toInt(n) | Lock l <- locks.locks, (LId)`@<Num n>` := l.id ],
    int n := ((ns == []) ? 0 : 1 + max(ns)),
    Num id := [Num]"<n>";

Locks addLock((Locks)`<Lock* locks>`, Lock lock)
  = (Locks)`<Lock* locks>
           '<Lock lock>`;
  
Locks deleteLock((Locks)`<Lock* ls1> <Lock l> <Lock* ls2>`, LId lock)
  = (Locks)`<Lock* ls1> <Lock* ls2>`
  when l.id == lock;

Lock getLock((Locks)`<Lock* ls1> <Lock l> <Lock* ls2>`, LId lock)
  = l
  when l.id == lock;  


Lock makeLock(Id i, list[Obj] reads, list[Obj] writes) {
  Lock l = (Lock)`<LId i> { | }`;
  for (Obj obj <- reads, (Lock)`<LId _> {<Obj* rs> | }` := l) {
    l = (Lock)`<LId i> {<Obj obj> <Obj* rs> | }`;
  }
  for (Obj obj <- writes, (Lock)`<LId _> {<Obj* rs> | <Obj* ws>}` := l) {
    l = (Lock)`<LId i> {<Obj* rs> | <Obj obj> <Obj* ws>}`;
  }
  return l;
}

// why yu no work?
//Lock makeLock(Id i, list[Obj] _:[], list[Obj] _:[])
//  =  (Lock)`<Id i> {|}`;
//
//Lock makeLock(Id i, list[Obj] _:[], list[Obj] _:[Obj x, *list[Obj] xs]) 
//  = (Lock)`<Id i> {<Obj* rs> | <Obj x> <Obj* ws>}`
//  when
//    (Lock)`<Id _> {<Obj* rs> | <Obj* ws>}` := makeLock(i, [], xs);
//
//Lock makeLock(Id i, list[Obj] _:[Obj x, *list[Obj] xs], list[Obj] writes) 
//  = (Lock)`<Id i> {<Obj x> <Obj* rs>| <Obj* ws>}`
//  when
//    (Lock)`<Id _> {<Obj* rs> | <Obj* ws>}` := makeLock(i, xs, writes);


bool isWriteLockedExcept((Locks)`<Lock* ls>`, Ref r, set[LId] exc)
  = ( false | it || (obj.ref == r && l.id notin exc) | Lock l <- ls, Obj obj <- l.writes );

bool isReadLockedExcept((Locks)`<Lock* ls>`, Ref r, set[LId] exc)
  = ( false | it || (obj.ref == r && l.id notin exc) | Lock l <- ls, Obj obj <- l.reads );

bool isWriteLocked((Locks)`<Lock* ls>`, Ref r)
  = ( false | it || obj.ref == r | Lock l <- ls, Obj obj <- l.writes );

bool isReadLocked((Locks)`<Lock* ls>`, Ref r)
  = ( false | it || obj.ref == r | Lock l <- ls, Obj obj <- l.reads );

Obj lookup(Store s, Ref r) = [ obj | Obj obj <- s.objs, obj.ref == r ][0];

Store update((Store)`<Obj* os1> <Obj old> <Obj* os2>`, Obj obj) =
   (Store)`<Obj* os1>
          '<Obj obj> 
          '<Obj* os2>`
   when old.ref == obj.ref;

Store addObj((Store)`<Obj* os>`, Obj obj) 
  = (Store)`<Obj* os> 
           '<Obj obj>`;
   
Obj gotoState(Obj obj, Id x) = obj[state=(St)`<Id x>`];


Value getField(Obj obj, Id x) 
  = [ p.val | Prop p <- obj.props, p.name == x ][0]; 

Obj setField((Obj)`<Ref r>: <Id c> [<St s>] {<{Prop ","}* ps1>, <Prop p>, <{Prop ","}* ps2>}`, Id x, Value v) 
 = (Obj)`<Ref r>: <Id c> [<St s>] {<{Prop ","}* ps1>, <Prop p2>, <{Prop ","}* ps2>}`
   when p.name == x, Prop p2 := p[val=v];

default Obj setField((Obj)`<Ref r>: <Id c> [<St s>] {<{Prop ","}* ps>}`, Id x, Value v) 
 = (Obj)`<Ref r>: <Id c> [<St s>] {<{Prop ","}* ps>, <Id x>: <Value v>}`;

Obj isInitialized(Obj obj) = (St)`⊥` !:= obj.state;

Entity lookupEntity(Spec spec, Id name)
  = [ e | Entity e <- spec.entities, e.name == name ][0];

State lookupState(Entity e, (St)`⊥`)
  = [ s | s:(State)`init <Transitions _>` <- e.states ][0];

State lookupState(Entity e, (St)`<Id name>`)
  = [ s | State s <- e.states, (State)`init <Transitions _>` !:= s, s.name == name ][0];

// TODO: make this nicer...
bool hasTransition(State s, Id name)
  = [ t | (State)`final <Id _>;` !:= s, /Trans t := s.transitions, t.name == name ] != [];

Trans lookupTransition(State s, Id name)
  = [ t | (State)`final <Id _>;` !:= s, /Trans t := s.transitions, t.name == name ][0];

list[Trans] lookupTransitions(State s) 
  = [ t | (State)`final <Id _>;` !:= s, /Trans t := s.transitions ];

// assumes trans has been normalized
Id getTarget((Trans)`on <Id _>(<{Formal ","}* _>): <Id x> <Pre _> <Stmt _>`)
  = x; 

// assumes trans has been normalized
Expr getPre((Trans)`on <Id _>(<{Formal ","}* _>): <Id x> require <Expr x> <Stmt _>`)
  = x; 

set[Ref] reachableRefs(Store s, Stmt stmt) {
  set[Ref] rs = {};
  
  visit (stmt) {
    case x: ;
  }
}

bool bprintSub(map[Expr, Expr] sub) {
 for (k <- sub) {
   println("<k> =\> <sub[k]>");
 }
 return true;
}

Stmt subst(map[Expr, Expr] sub, Stmt s) {
  return top-down-break visit (s) {
    
    case t:(Stmt)`let <Id x> = <Expr _> in <Stmt s>` => t
      when (Expr)`<Id x>` in sub
       
    case Expr e => sub[e] when e in sub
  
  }
}

Expr subst(map[Expr, Expr] sub, Expr expr) {
  return visit (expr) {
    case Expr e => sub[e] when e in sub
  }
}

map[Expr, Expr] makeSubst({Formal ","}* fs, {Expr ","}* es) {
  list[Expr] vars = [ (Expr)`<Id x>` | Formal f <- fs, Id x := f.var ]; 
  list[Expr] args = [ e | Expr e <- es ];
  return ( vars[i]: args[i] | int i <- [0..size(vars)] ); 
}
  
int toInt(Num i) = toInt("<i>");

Expr intExpr(int n) = (Expr)`<Num i>` when Num i := [Num]"<n>";

Expr boolExpr(bool b) = b ? (Expr)`true` : (Expr)`false`;

