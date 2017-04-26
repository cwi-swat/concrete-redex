module Redex

import util::IDE;
import ParseTree;

extend lang::rascal::\syntax::Rascal;

start syntax Spec
  = Section*;
  
syntax Section
  = "variables" {VarDecl ";"}*
  | "rules" Rule*
  ;
  
syntax VarDecl
  = varDecl: {Name ","}* names ":" Name sort;

lexical VarName
  = Name [\']*
  ;
  

syntax Pattern
  = Name "[" Pattern "]"
  | term: Term
  ;  

syntax Term
  = Pattern!term
  ;  
  
  
syntax Rel
  = Pattern "~\>" Pattern
  ;  
  
syntax Rule
  = Header  Rel When? "."
  ;
  

lexical Bar
  = "---"[\-]* !>> [\-]
  ;

syntax Header
  = {Rel ","}+ "[" Name "]" Bar
  | {Rel ","}+  Bar "[" Name "]" 
  | "[" Name "]"
  ;  
  
  
syntax When
  = "when" {Expression ","}*
  ;

// TODO: merge

syntax Term 
  = "true"
  | "false"
  | "if" Term "then" Term "else" Term "fi"
  | "z"
  | "succ" "(" Term ")"
  | "pred" "(" Term ")"
  | "isZero" "(" Term ")"
  // reusing term syntax for contexts as well
  | "☐"
  ;

syntax Term = @category="MetaVariable" VarName;

void registerRedex() {
  registerLanguage("Redex", "redex", start[Spec](str src, loc org) {
    return parse(#start[Spec], src, org, allowAmbiguity = true);
  });
}