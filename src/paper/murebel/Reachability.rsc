module paper::murebel::Reachability

import paper::murebel::Contexts;
import paper::murebel::Syntax;
import util::Maybe;


@doc{Find the immediately enclosing sync block around the hole.}
Maybe[S] innerMostSync(S ctx, Maybe[S] sync) {
  Maybe[S] result = sync;
  
  top-down-break visit (ctx) {
    case s:(S)`sync (<{Id ","}* _>) <S c>`:
      if (just(S found) := innerMostSync(c, just(s))) 
        return just(found);
      else
        fail;
     
    case S s: 
      if (s is hole) return sync; else fail; 
  }
  
  return result;
}

// find heap addresses possibly modified by stmt
// assume there are no free vars in stmt
// do we need fixpoint here? probably not, because no loops/recursion

alias RW = tuple[set[Ref] reads, set[Ref] writes];

@doc{Do an abstract interpretation of stmt to find which references
are read from and which ones are modified.}
RW reachable(Stmt stmt, Store s, Spec spec) {
  RW result = <{}, {}>;
  
  top-down-break visit(stmt) {
    case Expr e: 
      result.reads += reads(e, s);

    case (Stmt)`let <Id x> = <Expr e> in <Stmt b>`: { 
      <rs, ws> = reachable(subst((Expr)`<Id x>`, e, b), s, spec);
      result.reads += rs;
      result.writes += ws;
    }
    

    case (Stmt)`<Expr e>.<Id x>(<{Expr ","}* args>);`: {
      result.reads += reads(e, s);
      if (just(Ref r) := eval(e, s)) { 
       result.writes += {r};
       Obj obj = lookup(s, r);
        St cur = obj.state;
        Entity ent = lookupEntity(spec, obj.class);
        State st = lookupState(ent, cur);
        if (hasTransition(st, x)) {
          Trans t = normalize(lookupTransition(st, x), cur);
          {Formal ","}* fs = t.formals;
          if (arity(fs) == arity(args)) {
            Id trg = getTarget(t);
            map[Expr, Expr] sub = makeSubst(fs, args) + ((Expr)`this`: (Expr)`<Ref r>`);
            Stmt body = subst(sub, t.body);
            <rs, ws> = reachable(body, s, spec);
            result.reads += rs;
            result.writes += ws;
          }
       }
     }
    } 
    
    case (Stmt)`<Expr e>.<Id x> = <Expr a>;`: {
       result.writes += { r | just(Ref r) := eval(e, s) };
       result.reads += reads(e, s) + reads(a, s);
    } 
  }
  
  return result;
}

set[Ref] reads1((Expr)`<Expr e>.<Id x>`, Store s)
  = {r}
  when 
    just(Ref r) := eval(e, s),
    (Value)`<Ref t>` := getField(lookup(s, r), x);

set[Ref] reads1((Expr)`<Ref r>`, Store s)
  = {r};

default set[Ref] reads1(Expr e, Store s)
  = {};

set[Ref] reads(Expr e, Store s) 
  = ( {} | it + reads1(x, s) | /Expr x := e ); 
   

Maybe[Ref] eval((Expr)`<Expr e>.<Id x>`, Store s) 
  = just(t)
  when 
    just(Ref r) := eval(e, s),
    (Value)`<Ref t>` := getField(lookup(s, r), x);
    

Maybe[Ref] eval((Expr)`<Ref r>`, Store s) = just(r); 

default Maybe[Ref] eval(Expr _, Store _) = nothing();    
