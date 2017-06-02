module paper::murebel::Reachability

import paper::murebel::Contexts2;
import util::Maybe;
import ParseTree;
import IO;


@doc{Find the immediately enclosing sync block around the hole.}
Maybe[S] innerMostSync(S ctx, Maybe[S] sync) {
  Maybe[S] result = sync;
  
  top-down-break visit (ctx) {
    case s:(S)`sync (<{LId ","}* _>) <S c>`:
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

Expr conj((Expr)`true`, Expr e) = e;

Expr conj(Expr e, (Expr)`true`) = e;

default Expr conj(Expr e1, Expr e2) = (Expr)`<Expr e1> && <Expr e2>`;


Stmt seq((Stmt)`{<Stmt* ss1>}`, (Stmt)`{<Stmt* ss2>}`) 
  = (Stmt)`{<Stmt* ss1> <Stmt* ss2>}`;

Stmt seq(Stmt s1, (Stmt)`{<Stmt* ss2>}`) 
  = (Stmt)`{<Stmt s1> <Stmt* ss2>}`
  when !(s1 is block);

Stmt seq((Stmt)`{<Stmt* ss1>}`, Stmt s2) 
  = (Stmt)`{<Stmt* ss1> <Stmt s2>}`
  when !(s2 is block);

Stmt seq((Stmt)`;`, Stmt s) = s;
Stmt seq(Stmt s, (Stmt)`;`) = s;

default Stmt seq(Stmt s1, Stmt s2) = (Stmt)`{<Stmt s1> <Stmt s2>}`;

tuple[Expr, Stmt] flatten(Ref r, Id x, {Expr ","}* args, Store s, Spec spec) {
  Obj obj = lookup(s, r);
  St cur = obj.state;
  Entity ent = lookupEntity(spec, obj.class);
  println("ENTITY: <ent>");
  println("CUR: <cur>");
  State st = lookupState(ent, cur);
  Trans t = normalize(lookupTransition(st, x), cur);
  {Formal ","}* fs = t.formals;
  Id trg = getTarget(t);
  map[Expr, Expr] sub = makeSubst(fs, args) + ((Expr)`this`: (Expr)`<Ref r>`);
  Stmt body = subst(sub, t.body);
  <pre0, stmt> = flatten(body, s, spec);
  Expr pre = subst(sub, getPre(t));
  return <conj(pre0, pre), seq(stmt, (Stmt)`<Ref r> goes to <Id trg>;`)>;  
}

tuple[Expr, Stmt] flatten((Stmt)`<Ref r>.<Id x>(<{Expr ","}* args>);`, Store s, Spec spec) 
  = flatten(r, x, args, s, spec);

tuple[Expr, Stmt] flatten((Stmt)`let <Id x> = <Expr e> in <Stmt b>`, Store s, Spec spec) 
  = <pre, (Stmt)`let <Id x> = <Expr e> in <Stmt body>`>
  when <pre, body> := flatten(b, s, spec);

tuple[Expr, Stmt] flatten((Stmt)`{<Stmt* ss>}`, Store s, Spec spec) {
  res = <(Expr)`true`, (Stmt)`;`>;
  for (Stmt stmt <- ss) {
    <pre, body> = flatten(stmt, s, spec);
    res[0] = conj(res[0], pre); 
    res[1] = seq(res[1], body);
  }
  return res;
} 

default tuple[Expr, Stmt] flatten(Stmt stmt, Store s, Spec spec)
  = <(Expr)`true`, stmt>;


@doc{Do an abstract interpretation of stmt to find which references
are read from and which ones are modified.}
RW reachable(Stmt stmt, Store s, Spec spec) {
  RW result = <{}, {}>;
  
  top-down-break visit(stmt) {
    case Expr e: 
      result.reads += reads(e, s);

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
