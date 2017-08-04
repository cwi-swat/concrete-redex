module paper::Contextual

extend lang::std::Layout;
extend lang::std::Id;

start syntax Contexts
  = Rule*
  ;

syntax Rule
  = "context" Id "[" Id "]" "=" {Pat "|"}+ ";"
  ;

// semantic restriction: every alt pattern must have 1 path
// to hole, (e.g. ref must be to context when used at top-level).
// Context refs cannot be in regulars.  
syntax Pat
  = hole: "☐" // to avoid amb with empty list.
  | cons: Id "(" {Pat ","}* ")"
  | plug: Id "[" Pat "]"
  | ref: Id
  | lst: "[" {Pat ","}* "]"
  | non-assoc (
    star: Pat!star "*"  
  | plus: Pat!plus "+"  
  | opt: Pat!opt "?"
  )  
  ;

//Pat plug(Rule r, Pat h) = visit (r) { case (Pat)`☐` => h };
//  
//list[Pat] flatten(Rule rule) {
//  for (Pat alt <- rule.alts) {
//    visit (alt) {
//      case (Pat)`[<{Pat ","}* ps1>, <Pat p>*, <{Pat ","}* ps2>]`:; 
//    }
//  }
//}
  
/*
Translate to grammar
  hole => given at context definition or at call site

  context E[Expr]
    ===> 
  syntax E[Expr]
    = Expr // unfold to syntax for the abstract syntax ADT of Expr
    | "apply" "(" ... ")" etc.  
  
  in a list: need to take care of separators!!!
  X* ==> {X ","}*
  X+ ==> {X ","}+
  
  Flatten them out:
  e.g.
    f([X*]) ==> f([]) and f(X+)
    
  E[X] => E1, where hole is replaced with X 
  

*/