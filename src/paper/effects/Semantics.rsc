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

syntax Stream
  = Value*;

syntax Conf
  = Stream input ";" Stream output "|-" Computation
  ;
  
syntax C
  = Stream input ";" Stream output "|-" E
  ;


CR red("do1", C ctx, (Computation)`do <Id x> ⟵ return <Value v> in <Computation c>`)
  = {<ctx, subst((Value)`<Id x>`, v, c)>};
  
CR red("do2", C ctx, (Computation)`do <Id x> ⟵ <Op op>(<Value v>; <Id y>.<Computation c1>) in <Computation c2>`)
  = {<ctx, (Computation)`<Op op>(<Value v>; <Id y>. do <Id x> ⟵ <Computation c1> in <Computation c2>)`>};

CR red("ifT", C ctx, (Computation)`if true then <Computation c1> else <Computation c2>`)
  = {<ctx, c1>};  

CR red("ifF", C ctx, (Computation)`if false then <Computation c1> else <Computation c2>`)
  = {<ctx, c2>};  

CR red("apply", C ctx, (Computation)`fun <Id x> ↦ <Computation c> <Value v>`)
  = {<ctx, subst((Value)`<Id x>`, v, c)>};

CR red("applyPair", C ctx, (Computation)`fun (<Id x>, <Id y>) ↦ <Computation c> (<Value v1>, <Value v2>)`)
  = {<ctx, subst((Value)`<Id y>`, v2, subst((Value)`<Id x>`, v1, c))>};


CR red("opApply", C ctx, (Computation)`<Op op> <Value v>`)
  = {<ctx, (Computation)`fun x ↦ <Op op>(x; y. return y) <Value v>`>};
  
CR red("desugarSeq", C ctx, c:(Computation)`<Computation c1>; <Computation c2>`)
  = {<ctx, (Computation)`do <Id x> ⟵ <Computation c1> in <Computation c2>`>}
  when
    Id x := fresh((Id)`x`, { x | /Id x := c });
  

CR red("hReturn", C ctx, (Computation)`with <Handler h> handle return <Value v>`)
  = {<ctx, subst((Value)`<Id x>`, v, h.cr)>}
  when Id x := h.x;

  
// TODO: clean this mess up.
CR red("hOp1", C ctx, (Computation)`with <Handler h> handle <Op op>(<Value v>; <Id y>.<Computation c>)`)
  = {<ctx, subst((Value)`<Id k>`, (Value)`fun <Id y> ↦ with <Handler h> handle <Computation c>`, cr)>}
  when 
    list[Clause] cls := [ c | Clause c <- h.clauses, c.op == op ],
    cls != [], 
    (Clause)`<Op _>(<Id x>; <Id k>) ↦ <Computation ci>` := cls[0],
    Computation cr := subst((Value)`<Id x>`, v, ci);

CR red("hOp1", C ctx, (Computation)`with <Handler h> handle <Op op>(<Value v>; <Id y>.<Computation c>)`)
  = {<ctx, subst((Value)`<Id k>`, (Value)`fun <Id y> ↦ with <Handler h> handle <Computation c>`, ci)>}
  when 
    list[Clause] cls := [ c | Clause c <- h.clauses, c.op == op ],
    cls != [], 
    (Clause)`<Op _>(_; <Id k>) ↦ <Computation ci>` := cls[0];

CR red("hOp2", C ctx, (Computation)`with <Handler h> handle <Op op>(<Value v>; <Id y>.<Computation c>)`)
  = {<ctx, (Computation)`<Op op>(<Value v>; <Id y>. with <Handler h> handle <Computation c>)`>}
  when 
    [ c | Clause c <- h.clauses, c.op == op ] == []; 

CR red("print_", C ctx, (Computation)`print_ <Value v>`)
  = {<ctx[output=vs2], (Computation)`return ()`>}
  when 
    (Stream)`<Value* vs>` := ctx.output,
    Stream vs2 := (Stream)`<Value* vs> <Value v>`;  

CR red("read_", C ctx, (Computation)`read_ <Value _>`)
  = {<ctx[input=(Stream)`<Value* vs>`], (Computation)`return <Value v>`>}
  when (Stream)`<Value* vs> <Value v>` := ctx.input; 

default CR red(str _, C _, Tree _) = {};

R reduceEff(Conf c) = reduce(#C, #Conf, red, c, {"do1", "do2", "ifT", "ifF", 
    "apply", "applyPair", "hReturn", "opApply", "desugarSeq", "hOp1", "hOp2", "print_", "read_"});  

RR applyEff(Conf c) = apply(#C, #Conf, red, c, {"do1", "do2", "ifT", "ifF", 
    "apply", "applyPair", "hReturn", "opApply", "desugarSeq", "hOp1", "hOp2", "print_", "read_"});  

Conf small()
  = (Conf)` ; |- <Computation c>` 
  when Computation c := wrapWithIO((Computation)`print! "bla"; print! "foo"`);


Conf smallRead()
  = (Conf)`"bar" ; |- <Computation c>` 
  when Computation c := wrapWithIO((Computation)`read! ()`);

Conf example()
  = (Conf)`"Tijs" "van der Storm"; |- <Computation c>`
  when Computation c := wrapWithIO(printFullName());

Computation printFullName() 
  = (Computation)`print! "What is your first name?";
                 'do firstName ⟵ read! () in
                 'print! "What is your surname";
                 'do surName ⟵ read! () in 
                 'print! (firstName, surName)`;


Computation wrapWithIO(Computation c)
  = (Computation)`with <Value h> handle <Computation c>`
  when Value h := io();

Value io() = (Value)`handler { 
                    '  return x ↦ return x,
                    '  print!(x; k) ↦ print_ x; k (), 
                    '  read!(_; k) ↦ do x ⟵ read_ () in k x 
                    '}`;

//Value printIt() = (Value)`handler { print!(x; k) ↦ print_ x; k s }`;
//Value readIt() = (Value)`handler { read!(_; k) ↦ do x ⟵ read_ () in k x  }`;

//Value alwaysRead() = (Value)`fun s ↦ return handler { read!(_; k) ↦ k s }`;
//  
//Computation withBob() = (Computation)
//`do alwaysRead ⟵ return <Value ar> in
//'do v ⟵ alwaysRead "Bob" in
//'with v handle <Computation pfn>`  
//  when 
//    Value ar := alwaysRead(),
//    Computation pfn := printFullName();
//  
