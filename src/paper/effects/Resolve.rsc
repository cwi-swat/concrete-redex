module paper::effects::Resolve

import paper::effects::Syntax;

import paper::Substitution;
import ParseTree;


Refs resolve((Value)`<Id x>`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, s, d> | <loc s, loc d> <- lu(x, x@\loc, envs) };

Refs resolve((Value)`fun <Id x> ↦ <Computation c>`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, c@\loc, x@\loc>}
  + resolveC(c, [{<c@\loc, x@\loc, x>}] + envs, lu);

Refs resolve((Value)`fun (<Id x>, <Id y>) ↦ <Computation c>`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, c@\loc, x@\loc>, <y@\loc, y, c@\loc, y@\loc>}
  + resolveC(c, [{<c@\loc, x@\loc, x>, <c@\loc, y@\loc, y>}] + envs, lu);

Refs resolve((Value)`(<Value v1>, <Value v2>)`, list[Env] envs, Lookup lu)
  = resolve(v1, envs, lu)
  + resolve(v2, envs, lu);

Refs resolve((Value)`handler { return <Id x> ↦ <Computation c>, <{Clause ","}* cs> }`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, c@\loc, x@\loc>}
  + resolveC(c, [{<c@\loc, x@\loc, x>}] + envs, lu)
  + ( {} | it + resolve(cl, envs, lu) | Clause cl <- cs );
  
Refs resolve((Clause)`<Op op>(<Id x>; <Id y>) ↦ <Computation c>`, list[Env] envs, Lookup lu)
  = {<x@\loc, x, c@\loc, x@\loc>, <y@\loc, y, c@\loc, y@\loc>}
  + resolveC(c, [{<c@\loc, x@\loc, x>, <c@\loc, y@\loc, y>}] + envs, lu);

Refs resolve((Clause)`<Op op>(_; <Id y>) ↦ <Computation c>`, list[Env] envs, Lookup lu)
  = {<y@\loc, y, c@\loc, y@\loc>}
  + resolveC(c, [{<c@\loc, y@\loc, y>}] + envs, lu);

default Refs resolve(Value _, list[Env] envs, Lookup lu)
  = {};
  
  

Refs resolveC((Computation)`return <Value v>`, list[Env] envs, Lookup lu)
  = resolve(v, envs, lu);
  
Refs resolveC((Computation)`<Op op>(<Value v>; <Id x>. <Computation c>)`, list[Env] envs, Lookup lu)
  = resolve(v, envs, lu)
  + {<x@\loc, x, c@\loc, x@\loc>}
  + resolveC(c, [{<c@\loc, x@\loc, x>}] + envs, lu);
 
Refs resolveC((Computation)`<Op op> <Value v>`, list[Env] envs, Lookup lu)
  = resolve(v, envs, lu);
 
Refs resolveC((Computation)`<Computation c1> ; <Computation c2>`, list[Env] envs, Lookup lu)
  = resolveC(c1, envs, lu) 
  + resolveC(c2, envs, lu);
  
Refs resolveC((Computation)`do <Id x> ⟵ <Computation c1> in <Computation c2>`, list[Env] envs, Lookup lu)
  = resolveC(c1, envs, lu)
  + {<x@\loc, x, c2@\loc, x@\loc>}
  + resolveC(c2, [{<c2@\loc, x@\loc, x>}] + envs, lu);
  
Refs resolveC((Computation)`if <Value v> then <Computation c1> else <Computation c2>`, list[Env] envs, Lookup lu)
  = resolve(v, envs, lu)
  + resolveC(c1, envs, lu)
  + resolveC(c2, envs, lu);
  
Refs resolveC((Computation)`<Value v1> <Value v2>`, list[Env] envs, Lookup lu)
  = resolve(v1, envs, lu)
  + resolve(v2, envs, lu);
  
Refs resolveC((Computation)`with <Value v> handle <Computation c>`, list[Env] envs, Lookup lu)
  = resolve(v, envs, lu)
  + resolveC(c, envs, lu);
  
Refs resolveC((Computation)`(<Computation c>)`, list[Env] envs, Lookup lu)
  = resolveC(c, envs, lu);
  
// replace x with e in t
Computation subst(Value x, Value e, Computation t) = subst(#Computation, x, e, t, resolveC);
