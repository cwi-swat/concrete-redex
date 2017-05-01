module app::ViewTrace

import salix::App;
import salix::HTML;
import salix::lib::Dagre;
import salix::lib::Highlight;

import IO;
import util::Math;
import Set;
import List;
import RRedex;
import ParseTree;

alias Model = tuple[rel[Tree,str,Tree,Tree] trace];

App[Model] viewTrace(rel[Tree,str,Tree,Tree] trace)
  = app(Model() { return <trace>; }, view, update, |http://localhost:7223|, |project://concrete-redex/src/app|);

data Msg;



Model update(Msg msg, Model m) = m;

// http://stackoverflow.com/questions/26348038/svg-foreignobjects-draw-over-all-other-elements-in-chrome?rq=1

lrel[str,str] reductCSS(Tree t) {
  if (t@reduct?) {
    return [<"border", "1px">, <"border-style", "solid">, <"display", "inline-block">];
  }
  return [];
}

void view(Model m) {
  div(() {
    
    h2("View trace");
    
    int id = 0;
    map[Tree, str] nodeIds = ();
    for (Tree n <- m.trace<0> + m.trace<3>) {
      nodeIds[n] = "<id>";
      id += 1;
    }
    
    dagre("mygraph", rankdir("TD"), width(1560), height(600), (N n, E e) {
      for (Tree x <- nodeIds) {
        n(nodeIds[x], shape("rect"), () { 
          highlightToHtml(x, container=pre, more = reductCSS);
        });
      }
      for (<Tree t1, str rule, Tree redex, Tree t2> <- m.trace) {
        e(nodeIds[t1], nodeIds[t2], edgeLabel("<rule>: <redex>"), lineInterpolate("linear"));
      }
    });    
    
  });
}