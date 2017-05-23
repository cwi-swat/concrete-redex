module paper::effects::Semantics

extend paper::ParseRedex;
import paper::effects::Syntax;
import paper::effects::Resolve;
import paper::Substitution;
import IO;

syntax E
  = "do" Pattern "⟵" E "in" Computation
  | "with" Value "handle" E
  | hole: Computation
  ;


CR red("doReturn", E ctx, (Computation)`do <Id x> ⟵ return <Value v> in <Computation c>`)
  = {<ctx, subst((Value)`<Id x>`, v, c)>};
  
CR red("do", E ctx, (Computation)`do <Id x> ⟵ <Op op>(<Value v>; <Id y>.<Computation c1>) in <Computation c2>`)
  = {<ctx, (Computation)`<Op op>(<Value v>; <Id y>. do <Id x> ⟵ <Computation c1> in <Computation c2>)`>};

CR red("ifT", E ctx, (Computation)`if true then <Computation c1> else <Computation c2>`)
  = {<ctx, c1>};  

CR red("ifF", E ctx, (Computation)`if false then <Computation c1> else <Computation c2>`)
  = {<ctx, c2>};  

CR red("apply", E ctx, (Computation)`fun <Id x> ↦ <Computation c> <Value v>`)
  = {<ctx, subst((Value)`<Id x>`, v, c)>};

CR red("applyPair", E ctx, (Computation)`fun (<Id x>, <Id y>) ↦ <Computation c> (<Value v1>, <Value v2>)`)
  = {<ctx, subst((Value)`<Id y>`, v2, subst((Value)`<Id x>`, v1, c))>};


CR red("desugarOp", E ctx, (Computation)`<Op op> <Value v>`)
  = {<ctx, (Computation)`fun <Id x> ↦ <Op op>(<Id x>; y. return y) <Value v>`>}
  when
    Id x := fresh((Id)`x`, { x | /Id x := v });
  
CR red("desugarSeq", E ctx, c:(Computation)`<Computation c1>; <Computation c2>`)
  = {<ctx, (Computation)`do <Id x> ⟵ <Computation c1> in <Computation c2>`>}
  when
    Id x := fresh((Id)`x`, { x | /Id x := c });
  

CR red("withReturn", E ctx, (Computation)`with <Handler h> handle return <Value v>`)
  = {<ctx, subst((Value)`<Id x>`, v, h.cr)>}
  when Id x := h.x;

  
CR red("withClause", E ctx, (Computation)`with <Handler h> handle <Op op>(<Value v>; <Id y>.<Computation c>)`)
  = {<ctx, subst((Value)`<Id k>`, (Value)`fun <Id y> ↦ with <Handler h> handle <Computation c>`, cr)>}
  when
    hasClause(op, h), 
    (Clause)`<Op _>(<Pattern p>; <Id k>) ↦ <Computation ci>` := getClause(op, h),
    Computation cr := bind(p, v, ci);

CR red("withNoClause", E ctx, (Computation)`with <Handler h> handle <Op op>(<Value v>; <Id y>.<Computation c>)`)
  = {<ctx, (Computation)`<Op op>(<Value v>; <Id y>. with <Handler h> handle <Computation c>)`>}
  when 
    !hasClause(op, h); 


default CR red(str _, E _, Tree _) = {};

set[str] effReductions() = {"doReturn", "do", "ifT", "ifF", "apply", "applyPair", "withReturn", 
                            "desugarOp", "desugarSeq", "withClause", "withNoClause"};

RR applyEff(Computation c) = apply(#E, #Computation, red, c, effReductions());  

// helper functions
Computation bind((Pattern)`<Id x>`, Value v, Computation c)
  = subst((Value)`<Id x>`, v, c);
  
Computation bind((Pattern)`_`, Value v, Computation c) = c;

bool hasClause(Op op, Handler h) = (Clause c <- h.clauses && c.op == op);

Clause getClause(Op op, Handler h) = [ c | Clause c <- h.clauses, c.op == op ][0];

