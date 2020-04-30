module lang::credex::demo::ql::Semantics

extend lang::credex::ParseRedex; // extend because parse bug

extend  lang::credex::demo::ql::QL;
extend lang::credex::demo::ql::Util;

syntax Stmt
  = "update" "(" Id "," Expr ")"
  | "updateVis" "(" Id "," Expr ")"
  | "updateVal" "(" Id "," Expr "," Value ")"
  | "{" Stmt* "}"
  ;  
  
syntax Conf
  = UI "," Question "⊢" Stmt stmt;
  
  
syntax C
  = UI ui "," Question qs "⊢" S;
  
syntax S
  = "update" "(" Id "," E ")"
  | "updateVis" "(" Id "," E ")"
  | "updateVal" "(" Id "," E "," Value ")"
  | "{" Stmt* S Stmt* "}" // interleaving
  | @hole "{" Stmt* "{" "}" Stmt* "}"
  | @hole "update" "(" Id "," Value ")"
  | @hole "updateVis" "(" Id "," Value ")"
  | @hole "updateVal" "(" Id "," Value "," Value ")"
  ;
  
syntax E
  = @hole Expr!value // call eval directly
  ;
  
CR red("update", C c, (S)`update(<Id x>, <Value v>)`)
  = {<c[ui=updateVal(c.ui, x, v)], makeBlock(c.qs, c.ui, x)>};

CR red("done", C c, (S)`{<Stmt* s1> { } <Stmt* s2>}`)
  = {<c, (Stmt)`{<Stmt* s1> <Stmt* s2>}`>};

CR red("updateVal-same", C c, (S)`updateVal(<Id x>, <Value v>, <Value old>)`)
  = {<c, (Stmt)`{}`>}
  when old == v;

CR red("updateVal-diff", C c, (S)`updateVal(<Id x>, <Value v>, <Value old>)`)
  = {<c, (Stmt)`update(<Id x>, <Value v>)`>}
  when old != v;

CR red("updateVis", C c, (S)`updateVis(<Id x>, <Bool b>)`)
  = {<c[ui=updateVis(c.ui, x, b)], (Stmt)`{}`>};
    
Stmt makeBlock((Question)`{}`, UI _, Id _) = (Stmt)`{}`;

Stmt makeBlock((Question)`{ <Question q> <Question* qs>}`, UI ui, Id x)
  = (Stmt)`{<Stmt* s1> <Stmt* s2>}`
  when 
    (Stmt)`{<Stmt* s1>}` := q2stmt(q, ui, x),
    (Stmt)`{<Stmt* s2>}` := makeBlock((Question)`{<Question* qs>}`, ui, x);
  
Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _>`, UI ui, Id x)
  = (Stmt)`{updateVis(<Id y>, <Expr cond>)}`
  when x in uses(cond);
  
Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _> = <Expr e>`, UI ui, Id x)
  = (Stmt)`{updateVis(<Id y>, <Expr cond>) updateVal(<Id y>, <Expr e>, <Value old>)}`
  when
    x in uses(cond),
    x in uses(e), 
    Value old := lookup(ui, y);

Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _> = <Expr e>`, UI ui, Id x)
  = (Stmt)`{updateVis(<Id y>, <Expr cond>)}`
  when
    x in uses(cond), x notin uses(e);

Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _> = <Expr e>`, UI ui, Id x)
  = (Stmt)`{updateVal(<Id y>, <Expr e>, <Value old>)}`
  when
    x in uses(e), x notin uses(cond),
    Value old := lookup(ui, y);
    
default Stmt q2stmt(Question _, UI _, Id _) = (Stmt)`{}`;

set[Id] uses(Expr e) = { x | /Id x := e };
  
CR red("eval", C c, (E)`<Expr e>`) = 
  {<c, (Expr)`<Value val>`>}
  when 
    value v := eval(e, c.ui),
    Value val := [Value]"<v>";

default CR red(str _, C _, Tree _) = {};

Conf initialConf(f:(Form)`form <Id _> { <Question* qs> }`, Stmt stmt, UI ui = initialUI(f))
  =  (Conf)`<UI ui>, {<Question* qs>} ⊢ <Stmt stmt>`;

RR applyQL(Conf c) = apply(#C, #Conf, red, c, 
  {"update", "eval", "done", "updateVal-same", "updateVal-diff", "updateVis"});

void redexSteps(Conf c, str indent = "") {
  //if (isVal(e)) {
  //  return;
  //}

  RR rr = applyQL(c);
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(rr) - 1 ? last : other> ";
    
  for (<str rule, Conf sub> <- rr) {
    println("<indented("└─", "├─")><c.stmt> \u001b[34m─<rule>→\u001b[0m <sub.stmt>");
    redexSteps(sub, indent = indented(" ", "│"));
    i += 1;
  }
}
   
Form example() = (Form)`form taxOfficeExample { 
'  if (true) "Did you sell a house in 2010?"
'    hasSoldHouse: boolean 
'  if (true) "Did you buy a house in 2010?"
'    hasBoughtHouse: boolean  
'  if (true) "Did you enter a loan?"
'    hasMaintLoan: boolean
' 
'  if (hasSoldHouse) 
'    "What was the selling price?"
'      sellingPrice: integer  
'  if (hasSoldHouse) 
'    "Private debts for the sold house:"
'      privateDebt: integer
'  if (hasSoldHouse) 
'    "Value residue:"  
'      valueResidue: integer = (sellingPrice - privateDebt) 
'}`;
   
