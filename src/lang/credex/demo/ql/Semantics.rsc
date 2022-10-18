module lang::credex::demo::ql::Semantics

extend lang::credex::ParseRedex; // extend because parse bug

extend  lang::credex::demo::ql::QL;
extend lang::credex::demo::ql::Util;

syntax Stmt
  = "update" "(" Id "," Expr ")" // a user action
  | "vis" "(" Id "," Expr ")" // update visibility
  
  // update value, third argument is the old value to detect changes 
  | "val" "(" Id "," Expr "," Value ")" 
  | "{" Stmt* "}"
  ;  
  
  
// a configuration consists of a UI (the state)
// a (block of) questions and a statement.  
syntax Conf
  = UI ui "," Question "⊢" Stmt stmt;
  
  
syntax C
  = UI ui "," Question qs "⊢" S;
  
syntax S
  = "update" "(" Id "," E ")"
  | "vis" "(" Id "," E ")"
  | "val" "(" Id "," E "," Value ")"
  | "{" S Stmt* "}" // sequential
  | @hole "{" "{" "}" Stmt* "}"
  | @hole "update" "(" Id "," Value ")"
  | @hole "vis" "(" Id "," Value ")"
  | @hole "val" "(" Id "," Value "," Value ")"
  ;

// expressions are "uninteresting" so we make
// their evaluation steps unobservable/silent.  
syntax E
  = @hole Expr!value // call eval directly
  ;

// dealing with unit of statement sequencing
CR red("done", C c, (S)`{ { } <Stmt* s2>}`)
  = {<c, (Stmt)`{ <Stmt* s2>}`>};

// a user action updates the ui state and
// then expands to a block of statements
// to reconcile the UI with the update  
CR red("update", C c, (S)`update(<Id x>, <Value v>)`)
  = {<c[ui=updateVal(c.ui, x, v)], makeBlock(c.qs, c.ui, x)>};

// updating a question to a value that is the same
// as the previous value is a no-op
CR red("val-same", C c, (S)`val(<Id x>, <Value v>, <Value old>)`)
  = {<c, (Stmt)`{}`>}
  when old == v;

// if the new value is different from the old one
// this is equivalent to a user action updating the question.
CR red("val-diff", C c, (S)`val(<Id x>, <Value v>, <Value old>)`)
  = {<c, (Stmt)`update(<Id x>, <Value v>)`>}
  when old != v;

// updating visibility modifies the UI
CR red("vis", C c, (S)`vis(<Id x>, <Bool b>)`)
  = {<c[ui=updateVis(c.ui, x, b)], (Stmt)`{}`>};
    
// expressions are immediately evaluated to values
CR red("eval", C c, (E)`<Expr e>`) = 
  {<c, (Expr)`<Value val>`>}
  when 
    value v := eval(e, c.ui),
    Value val := [Value]"<v>";

default CR red(str _, C _, Tree _) = {};

RR applyQL(Conf c) = apply(#C, #Conf, red, c, 
  {"update", "eval", "done", "val-same", "val-diff", "vis"});


/*
 * Auxiliar functions
 */    
    
Stmt makeBlock((Question)`{}`, UI _, Id _) = (Stmt)`{}`;

Stmt makeBlock((Question)`{ <Question q> <Question* qs>}`, UI ui, Id x)
  = (Stmt)`{<Stmt* s1> <Stmt* s2>}`
  when 
    (Stmt)`{<Stmt* s1>}` := q2stmt(q, ui, x),
    (Stmt)`{<Stmt* s2>}` := makeBlock((Question)`{<Question* qs>}`, ui, x);
  
// q2stmt produces update statements for a question if they
// are affected by the variable x (either in their condition or expression)
  
Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _>`, UI ui, Id x)
  = (Stmt)`{vis(<Id y>, <Expr cond>)}`
  when x in uses(cond);
  
Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _> = <Expr e>`, UI ui, Id x)
  = (Stmt)`{vis(<Id y>, <Expr cond>) val(<Id y>, <Expr e>, <Value old>)}`
  when
    x in uses(cond),
    x in uses(e), 
    Value old := lookup(ui, y);

Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _> = <Expr e>`, UI ui, Id x)
  = (Stmt)`{vis(<Id y>, <Expr cond>)}`
  when
    x in uses(cond), x notin uses(e);

Stmt q2stmt((Question)`if (<Expr cond>) <Label _> <Id y>: <Type _> = <Expr e>`, UI ui, Id x)
  = (Stmt)`{val(<Id y>, <Expr e>, <Value old>)}`
  when
    x in uses(e), x notin uses(cond),
    Value old := lookup(ui, y);
    
default Stmt q2stmt(Question _, UI _, Id _) = (Stmt)`{}`;

set[Id] uses(Expr e) = { x | /Id x := e };
  
Conf initialConf(f:(Form)`form <Id _> { <Question* qs> }`, Stmt stmt, UI ui = initialUI(f))
  =  (Conf)`<UI ui>, {<Question* qs>} ⊢ <Stmt stmt>`;

void redexSteps(Conf c, str indent = "") {
  //if (isVal(e)) {
  //  return;
  //}

  RR rr = applyQL(c);
  
  if (rr == {}) {
    for (UIElement e <- c.ui.elts) {
      println(e);
    }
  }
  
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(rr) - 1 ? last : other> ";
    
  for (<str rule, Conf sub> <- rr) {
    println("<indented("│ ", "│ ")><toString(c.ui)> ⊢"); 
    println("<indented("└─", "├─")><c.stmt> \u001b[34m─<rule>→\u001b[0m <sub.stmt>");
    redexSteps(sub, indent = indented(" ", "│"));
    i += 1;
  }
}

void runSimple(Stmt stm, Form form = simpleExample()) {
  c = initialConf(form, stm);
  redexSteps(c);
}
 
str toString(UI ui) =
 intercalate(", ", [ "<e.name><(Bool)`false` := e.visible ? "\'" : "">↦<e.val>" | UIElement e <- ui.elts ]); 
 
// with update(c, 10) this should evaluate to
// 10 + 11 + 1 = 22
// and eventuall b invisible but c visible
// (and intermittently this is swapped)  
Form simpleExample() = (Form)`form simple {
'  if (true) "A" a: integer = c + b + 1
'  if (a \< 20) "B" b: integer = c + 1
'  if (a \> 20) "C" c: integer
'}`;   

Form cyclicExample() = (Form)`form simple {
'  if (true) "A" a: integer = c + b + 1
'  if (true) "B" b: integer = c + 1
'  if (true) "C" c: integer = a + 1
'}`;   

   
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
   
