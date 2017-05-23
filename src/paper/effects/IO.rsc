module paper::effects::IO

import paper::effects::Semantics;
import paper::effects::Syntax;
extend paper::ParseRedex;

syntax Stream
  = Value*;

syntax Conf
  = Stream input ";" Stream output "⊢" Computation
  ;
  
syntax C
  = Stream input ";" Stream output "⊢" E
  ;

CR red("print", C ctx, (Computation)`print_ <Value v>`)
  = {<ctx[output=vs2], (Computation)`return ()`>}
  when 
    (Stream)`<Value* vs>` := ctx.output,
    Stream vs2 := (Stream)`<Value* vs> <Value v>`;  

CR red("read", C ctx, (Computation)`read_ <Value _>`)
  = {<ctx[input=(Stream)`<Value* vs>`], (Computation)`return <Value v>`>}
  when (Stream)`<Value* vs> <Value v>` := ctx.input; 
  

default CR red(str n, (C)`<Stream inp>; <Stream out> ⊢ <E e1>`, Computation c1)
  = { <(C)`<Stream inp>; <Stream out> ⊢ <E e2>`, c2> | <E e2, Computation c2> <- red(n, e1, c1) };
  
set[str] ioReductions() = effReductions() + {"print", "read"};  
  
RR applyIO(Conf c) = apply(#C, #Conf, red, c, ioReductions());  

Conf small()
  = (Conf)` ; ⊢ <Computation c>` 
  when Computation c := wrapWithIO((Computation)`print! "bla"; print! "foo"`);


Conf smallRead()
  = (Conf)`"bar" ; ⊢ <Computation c>` 
  when Computation c := wrapWithIO((Computation)`read! ()`);

Conf example()
  = (Conf)`"Smith" "John"; ⊢ <Computation c>`
  when Computation c := wrapWithIO(printFullName());
  
Conf reversedExample()
  = (Conf)` ; ⊢ with <Value r> handle <Computation abc>`
  when
    Value r := reversed(), 
    Computation abc := (Computation)`print! "A"; print! "B"; print! "C"`;

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



Value reversed() = (Value)`handler { 
                    '  return x ↦ return x,
                    '  print!(x; k) ↦  k (); print_ x, 
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
  