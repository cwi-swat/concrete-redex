module lang::credex::util::ViewTrace

import salix::App;
import salix::HTML;
import salix::lib::Dagre;
import salix::lib::Highlight;

import IO;
import util::Math;
import Set;
import List;
import ParseTree;

alias Model = tuple[rel[Tree,str,Tree] trace];

App[Model] viewTrace(rel[Tree,str,Tree] trace, loc root = |project://concrete-redex/src/lang/credex/util|)
  = app(Model() { return <trace>; }, view, update, |http://localhost:7228/index.html|, root);

data Msg;


Model update(Msg msg, Model m) = m;

// http://stackoverflow.com/questions/26348038/svg-foreignobjects-draw-over-all-other-elements-in-chrome?rq=1

//lrel[str,str] reductCSS(Tree t) {
//  if (t@reduct?) {
//    return [<"border", "1px">, <"border-style", "solid">, <"display", "inline-block">];
//  }
//  return [];
//}

Tree removeLayout(Tree t) {
  return t;
  return visit (t) {
    case appl(p:prod(layouts(_), _, _), list[Tree] args) =>
      appl(p, [char(32)])
  }
}

void view(Model m) {
  div(() {
    
    h2("View trace");
    
    int id = 0;
    map[Tree, str] nodeIds = ();
    for (Tree n <- m.trace<0> + m.trace<2>) {
      // BIG bug: == is modulo layout, but map indexing is not.
      nodeIds[removeLayout(n)] = "<id>";
      id += 1;
    }
    
    dagre("mygraph", rankdir("TD"), width(1560), height(600), (N n, E e) {
      for (Tree x <- m.trace<0> + m.trace<2>) {
        n(nodeIds[removeLayout(x)], shape("rect"), () { 
          highlightToHtml(x, container=pre);
        });
      }
      for (<Tree t1, str rule, Tree t2> <- m.trace) {
        e(nodeIds[removeLayout(t1)], nodeIds[removeLayout(t2)], edgeLabel("<rule>"), lineInterpolate("basis"));
      }
    });    
    
  });
}