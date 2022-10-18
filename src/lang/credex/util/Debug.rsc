module lang::credex::util::Debug

import lang::credex::TraceRedex;

import salix::App;
import salix::HTML;
import salix::lib::Dagre;
import salix::lib::Highlight;

import IO;
import util::Math;
import util::Maybe;
import Set;
import List;
import ParseTree;
import util::Reflective;

import lang::rascal::\syntax::Rascal;
import lang::credex::demo::imp::Semantics;
import lang::credex::demo::imp::Contexts;

App[Model] debugImp() {
  set[str] rules = {"leq", "seq", "if-true",
    "if-false", "lookup", "assign", "add", "div", "while", "not-false",
    "not-true", "and-true", "and-false"};
  RRRR myApply(Conf c) = applyWithRedex(#C, #Conf, red, c, rules); 
  return debugCredex(|project://concrete-redex/src/lang/credex/demo/imp/Semantics.rsc|, myApply, example(), rules); 
}

// todo: pass in red, not apply, and set of rules explicitly, now the set of rules is duplicated
App[Model] debugCredex(loc semantics, RRRR(&T<:Tree) apply, &T term, set[str] rules, loc root = |project://concrete-redex/src/lang/credex/util|)
  = app(makeInit(semantics, lift(apply), term, rules), debugView, updateDebugger, |http://localhost:7230/debug.html|, root);


RRRR(Tree) lift(RRRR(&T<:Tree) apply) {
  return RRRR(Tree x) {
     if (&T t := x) return apply(t);
     return {};
  };
}

FunctionDeclaration findRule(str rule, Tree semantics) {
  visit (semantics) {
    case f:(FunctionDeclaration)`<Tags _> <Visibility _> CR red(<StringLiteral ruleLit>, <{Pattern ","}* _>) = <Expression _>;`: 
      if ("<ruleLit>"[1..-1] == rule) return f;
       
    case f:(FunctionDeclaration)`<Tags _> <Visibility _> CR red(<StringLiteral ruleLit>, <{Pattern ","}* _>) = <Expression _> when <{Expression ","}+ _>;`:
      if ("<ruleLit>"[1..-1] == rule) return f;
  } 
  throw "no such rule: <rule>";
}

Maybe[tuple[Tree,Tree]] findRedex(Tree t1, Tree t2) {
  if (appl(Prod p1, list[Tree] args1) := t1, 
      appl(Prod p2, list[Tree] args2) := t2, p1 == p2) {
     for (int i <- [0..size(args1)]) {
       if (args1[i] != args2[i]) {
         return findRedex(args1[i], args2[i]);
       }
     }
     return nothing();   
  }
  return just(<t1, t2>);
}

Model() makeInit(loc semantics, RRRR(Tree) apply, Tree term, set[str] rules) {
  return Model() {
    // this stuff is all the same as in next(); Refactor!
    RRRR nxt = apply(term);
    maybeRule = nothing();
    sem = parseModuleAndFragments(semantics);
    pos = -1;
    if (<_, _, str nextRule, _> <- nxt) {
     // just pick one, for now
      maybeRule = just(findRule(nextRule, sem));
      pos = 0;
    }
    return <apply, sem, maybeRule, [config(term, toList(nxt))], pos, rules>;
  };
}

data Config
  = config(Tree source, lrel[Tree, Tree, str,Tree] results);

alias Model
  = tuple[
      RRRR(Tree) apply,
      Tree semantics,
      Maybe[FunctionDeclaration] currentRule,
      list[Config] trace,
      int position,
      set[str] rules
  ];
  

data Msg
  = next(str rule, int pos)
  | prev()
  | showRule(str rule)
  ;

Model updateDebugger(Msg msg, Model m) {
  switch (msg) {
    case next(str r, int pos): {
       if (m.position >= 0) {
         if (<_, _, str r, Tree t> := m.trace[m.position].results[pos]) {
           RRRR nxt = m.apply(t);
           // todo: make currentConfig
           m.trace += [config(t, toList(nxt))];
           m.position += 1;
           if (<_, _, str nextRule, _> <- nxt) {
             // just pick one, for now
             m.currentRule = just(findRule(nextRule, m.semantics));
           }
         }
       }
    }

    case prev(): {
        // TODO: refactor into function
      if (m.position > 0, <_, _, str nextRule, _> <- m.trace[m.position - 1].results) {
        // just pick one, for now
        m.currentRule = just(findRule(nextRule, m.semantics));
        m.position -= 1;
        m.trace = m.trace[0..-1]; // truncate
      }
    }

    case showRule(str r): {
      m.currentRule = just(findRule(r, m.semantics));
    }
  }
  return m;
}

//void viewResult(Tree redex, Tree reduct, str rule, Tree result, int i) {
//  button(\type("button"), class("btn btn-primary btn-sm"), onClick(next(rule, i)), "Step");
//  //button(\type("button"), class("btn btn-secondary btn-sm"), onClick(showRule(rule)), rule);  
//  highlightToHtml(result, container=pre);
//  //h6("Redex");
//  //highlightToHtml(redex, container=pre);
//  //h6("Contractum");
//  //highlightToHtml(reduct, container=pre);
//  table(class("table"), () {
//    thead(() {
//      tr(() {
//        th("Redex"); th("Rule"); th("Contractum");
//      });
//    });
//    tbody(() {
//      tr(() {
//        td(() { highlightToHtml(redex, container=pre); });
//        td(() {
//          button(\type("button"), class("btn btn-secondary btn-sm"), onClick(showRule(rule)), rule);
//        });  
//        td(() { highlightToHtml(reduct, container=pre); });
//      });
//    });
//  });
//}

void viewResults(Model model) {
  int i = 0;
  for (model.position >= 0, <Tree redex, Tree reduct, str rule, Tree result> <- model.trace[model.position].results) {
      h3("Contractum (via <rule>)");
      a(onClick(next(rule, i)), () {
        highlightToHtml(reduct, container=pre);
      });
      //button(\type("button"), class("btn btn-secondary btn-sm"), onClick(showRule(rule)), rule);
      hr();
      i += 1;
  }
  
  //table(class("table"), () {
  //  thead(() {
  //    tr(() {
  //      th("#"); th("Rule"); th("Contractum");
  //    });
  //  });
  //  tbody(() {
  //    for (model.position >= 0, <Tree redex, Tree reduct, str rule, Tree result> <- model.trace[model.position].results) {
  //      tr(() {
  //        td(() { 
  //          button(\type("button"), class("btn btn-secondary btn-sm"), onClick(next(rule, i)), "Step");
  //        });
  //        //td(() { highlightToHtml(redex, container=pre); });
  //        td(() {
  //          button(\type("button"), class("btn btn-secondary btn-sm"), onClick(showRule(rule)), rule);
  //        });  
  //        td(() { highlightToHtml(reduct, container=code); });
  //      });
  //      i += 1;
  //    }
  //  });
  //}); 
}

anno bool Tree@redex;

lrel[str,str] redexCSS(Tree t) {
  if (t@redex?) {
    return [<"border", "1px">, <"border-style", "solid">, <"display", "inline-block">];
  }
  return [];
}

Tree markedSource(Tree src, set[Tree] rxs) {
  for (Tree redex <- rxs) { 
    src = bottom-up-break visit (src) {
      case Tree t => t[@redex=true] 
        when t@\loc?, t@\loc == redex@\loc
    };
  }
  return src;
}

void viewSource(Model model) {
  Tree src = markedSource(model.trace[model.position].source, toSet(model.trace[model.position].results<0>));
  h3("Term");
  a(onClick(prev()), () {
    highlightToHtml(src, container=pre, more=redexCSS);
  });
  
 // table(class("table"), () {
 //   thead(() {
 //     tr(() {
 //       th("#"); th("Term"); 
 //     });
 //   });
 //   tbody(() {
 //     tr(() {
 //       td(() {
 //         button(\type("button"), class("btn btn-secondary btn-sm"), onClick(prev()), "Back");
 //       });
 //       td(() {
 //         highlightToHtml(model.trace[model.position].source, container=pre);
 //       });
 //    });
 //  });
 //});
}

void viewTrace(Model model) {
  ul(class("list-group"), () {
    // todo: show redex as main item, sub items are configs where result is reduct (not whole term).
    for (Config c <- model.trace) {
      li(class("list-group-item"), () {
        if (size(c.results) > 1) {
          ul(class("list-group"), () {
            for (<Tree redex, Tree reduct, str r, Tree _> <- c.results) {
              li(class("list-group-item"), () {
                em(r);
              });
            }
          });
        }
        else {
          if (<Tree redex, Tree reduct, str r, Tree _> <- c.results) {
            em(r);
          }      
        }
      });
    }
  });
}

void viewRule(Model model) {
  if (just(FunctionDeclaration rule) := model.currentRule) {
    highlightToHtml(rule, container=pre);
  }
}


void debugView(Model model) {
  div(() {
    //div(class("row"), () {
    //  div(class("col-md-12"), () {
    //    h3("Concrete Redex Debugger");
    //  });
    //});
    
    div(class("row"), () {
      
      div(class("col-lg-12"), () {
        div(class("container"), () {
          div(class("row"), () {
            div(class("col-lg-5"), () {
              viewSource(model);
            });
          
            div(class("col-lg-7"), () {
              viewResults(model); 
            });
          });
          
          hr();
          div(class("row"), () {
            div(class("col-lg-12"), () {
              div(() {
                for (str r <- model.rules) {
                  a(href("#"), onClick(showRule(r)), r);
                  span(" ");
                }
              });      
              viewRule(model);
            });
          });
        });
      });
      
      //div(class("col-2"), () {
      //  viewTrace(model);
      //});
      
    });
    
  });    
}
