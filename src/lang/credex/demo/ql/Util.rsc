module lang::credex::demo::ql::Util

extend lang::credex::demo::ql::QL;
import String;

syntax UIElement
  = "[" Bool visible "," Id name "]" Label label ":" Value val;
  
syntax UI
  = "ui" Id "{" UIElement* elts "}";
  

value eval((Expr)`<Id x>`, UI ui) {
  switch (lookup(ui, x)) {
    case (Value)`<Bool b>`: return ((Bool)`true` := b);
    case (Value)`<Integer i>` : return toInt("<i>");
    case (Value)`<String s>` : return "<s>";
  }
}
 
value eval((Expr)`(<Expr e>)`, UI ui) = eval(e, ui);

value eval((Expr)`<Integer x>`, UI ui) = toInt("<x>");

value eval((Expr)`true`, UI ui) = true;

value eval((Expr)`false`, UI ui) = false;

value eval((Expr)`<String x>`, UI ui) = "<x>"[1..-1];

value eval((Expr)`!<Expr e>`, UI ui) = !v 
  when 
    bool v := eval(e, ui);

value eval((Expr)`<Expr lhs> * <Expr rhs>`, UI ui) 
  =  v1 * v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);


value eval((Expr)`<Expr lhs> / <Expr rhs>`, UI ui)
  =  v1 / v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> + <Expr rhs>`, UI ui)
  =  v1 + v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> - <Expr rhs>`, UI ui) 
  =  v1 - v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> \> <Expr rhs>`, UI ui)
  =  v1 > v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> \>= <Expr rhs>`, UI ui)
  =  v1 >= v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> \< <Expr rhs>`, UI ui)
  =  v1 < v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> \<= <Expr rhs>`, UI ui)
  =  v1 <= v2
  when 
    int v1 := eval(lhs, ui),
    int v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> == <Expr rhs>`, UI ui)
  =  v1 == v2
  when 
    value v1 := eval(lhs, ui),
    value v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> != <Expr rhs>`, UI ui)
  =  v1 != v2
  when 
    value v1 := eval(lhs, ui),
    value v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> && <Expr rhs>`, UI ui)
  =  v1 && v2
  when 
    bool v1 := eval(lhs, ui),
    bool v2 := eval(rhs, ui);
    
value eval((Expr)`<Expr lhs> || <Expr rhs>`, UI ui)
  =  v1 || v2
  when 
    bool v1 := eval(lhs, ui),
    bool v2 := eval(rhs, ui);
  
Value lookup(UI ui, Id x) = lookup(ui.elts, x);

Value lookup(UIElement* elts, Id x)
  = [ e.val | UIElement e <- elts, x := e.name ][0];
  
UI updateVal(ui:(UI)`ui <Id u> {<UIElement* es1> [<Bool b>, <Id y>] <Label l>: <Value _> <UIElement* es2>}`, Id x, Value v)
 = (UI)`ui <Id u> {<UIElement* es1> [<Bool b>, <Id y>] <Label l>: <Value v> <UIElement* es2>}`
 when y == x;
  
UI updateVis(ui:(UI)`ui <Id u> {<UIElement* es1> [<Bool _>, <Id y>] <Label l>: <Value v> <UIElement* es2>}`, Id x, Bool b)
 = (UI)`ui <Id u> {<UIElement* es1> [<Bool b>, <Id y>] <Label l>: <Value v> <UIElement* es2>}`
 when y == x;
 
 
Value defaultValue((Type)`boolean`) = (Value)`false`;
 
Value defaultValue((Type)`integer`) = (Value)`0`;

Value defaultValue((Type)`string`) = (Value)`""`;
 
 
UI initialUI((Form)`form <Id x> {}`)
  = (UI)`ui <Id x> {}`;

UI initialUI((Form)`form <Id x> { <Question q> <Question* qs>}`)
  = (UI)`ui <Id x> {<UIElement elt>
        '  <UIElement* elts>}`
  when
    UIElement elt := initialElt(q),
    (UI)`ui <Id _> {<UIElement* elts>}` := initialUI((Form)`form <Id x> {<Question* qs>}`);

UIElement initialElt((Question)`if (<Expr _>) <Label l> <Id x>: <Type t>`)
  = (UIElement)`[true, <Id x>] <Label l> : <Value v>`
  when 
    Value v := defaultValue(t);    

UIElement initialElt((Question)`if (<Expr _>) <Label l> <Id x>: <Type t> = <Expr _>` )
  = (UIElement)`[true, <Id x>] <Label l> : <Value v>`
  when 
    Value v := defaultValue(t);    