module EvalCtx

extend lang::std::Layout;
import IO;
import Set;
import List;
import ParseTree;

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

syntax Term
  = Var "[" Term "]"
  | Var
  ;

lexical Var
  = @category="MetaVariable" x: [A-Z][0-9]* !>> [A-Z0-9]
  ;
  
// Alternative
syntax Ctx
  = "if" Ctx "then" Term "else" Term "fi"
  | "succ" "(" Ctx ")"
  | "pred" "(" Ctx ")"
  | "isZero" "(" Ctx ")"
  | "☐"
  ; 

syntax Rule
  = Term lhs "~\>" Term rhs
  ;

//// TODO: used reified grammar for this.  
map[Term, int] CTX
  = ((Term)`if ☐ then ☐ else ☐ fi`: 2,
     (Term)`succ(☐)`: 4,
     (Term)`pred(☐)`: 4,
     (Term)`isZero(☐)`: 4);
  
bool isValue((Term)`true`) = true;
bool isValue((Term)`false`) = true;
bool isValue((Term)`z`) = true;
bool isValue((Term)`succ(<Term t>)`) = isValue(t);
default bool isValue(Term _) = false;





bool isRedex((Term)`if true then <Term _> else <Term _> fi`) = true;
bool isRedex((Term)`if false then <Term _> else <Term _> fi`) = true;
bool isRedex((Term)`pred(succ(<Term t>))`) = true when isValue(t);
bool isRedex((Term)`isZero(z)`) = true;
bool isRedex((Term)`isZero(succ(<Term t>))`) = true when isValue(t);
default bool isRedex(Term _) = false;
  
/*

context Ctx: Term
  = "if" Ctx "then" Term "else" Term "fi"
  | "succ" "(" Ctx ")"
  | "pred" "(" Ctx ")"
  | "isZero" "(" Ctx ")"
  | ☐
  ;

reductions Simple
  = ifTrue:
      T1 ~> T2
      ------ 
      E[if true then T2 else T3 fi] ~> E[T2]
      
  | ifFalse: E[if false then T2 else T3 fi] ~> E[T3]
  | pred: E[pred(succ(T))] ~> E[T] when isValue(t)
  | isZeroZ: E[isZero(z)] ~> E[true]
  | isZero: E[isZero(succ(T))] ~> E[false] when isValue(t)
  ;

*/  
  

public set[Rule] REDUCTION = {
  (Rule)`E[if true then T2 else T3 fi] ~\> E[T2]`,
  (Rule)`E[if false then T2 else T3 fi] ~\> E[T3]`,
  (Rule)`E[pred(succ(T))] ~\> E[T]`, // when isValue(t);
  (Rule)`E[isZero(z)] ~\> E[true]`,
  (Rule)`E[isZero(succ(T))] ~\> E[false]` // when isValue(t);
};

  
  
// no stores or first-class contexts needed, so don't use them.
Term reduce((Term)`if true then <Term t2> else <Term t3> fi`) = t2;
Term reduce((Term)`if false then <Term t2> else <Term t3> fi`) = t3;
Term reduce((Term)`pred(succ(<Term t>))`) = t when isValue(t);
Term reduce((Term)`isZero(z)`) = (Term)`true`;
Term reduce((Term)`isZero(succ(<Term t>))`) = (Term)`false` when isValue(t);
default Term reduce(Term _) = {throw "error";};


Term updateCtx(Term ctx, int rec, Term kidCtx, Term t) {
  i = 0;
  //[i,i+2..size(ctx.args)];
  while (i < size(ctx.args)) {
    ctx = appl(ctx.prod, [*ctx.args[0..i], (i == rec) ? kidCtx : t.args[i], *ctx.args[i+1..]]);
    i += 2;
  }
  return ctx;
} 

// not sure about this.
rel[Term,Term] split(Term t) {
  result = {};
  for (Term ctx <- CTX) {
    int rec = CTX[ctx];
    if (ctx.prod == t.prod, Term kid := t.args[rec]) {
      result += { isRedex(t2) ? <updateCtx(ctx, rec, c2, t), t2> : <(Term)`☐`, t> | <Term c2, Term t2> <- split(kid) }; 
    }
  }
  if (result == {}) { // ????
    return {<(Term)`☐`, t>};
  }
  return result;
}

Term plug(Term ctx, Term t) = visit (ctx) { case (Term)`☐` => t }; 

Term example() = (Term)`if isZero(pred(succ(succ(z)))) then false else true fi`;

Term eval(Term t) {
  while (!isValue(t)) {
    println("Evaluating: <t>");
    t = getOneFrom(step(t));
  }
  return t;
}

bool log(Term ctx, Term redex) {
  println("Context: <ctx>");
  println("Redex: <redex>");
  return true;
}

// TODO: reduce itself is always deterministic now, but might need sets there too.
set[Term] step(Term t) = { plug(ctx, reduce(redex)) | <ctx, redex> <- split(t), log(ctx, redex) }; 

  