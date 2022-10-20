module PrettyTree

import IO;
import Node;
import List;
import ParseTree;

data Expr
  = lit(int n)
  | add(Expr l, Expr r)
  | mul(Expr l, Expr r)
  ;

Expr example() = add(mul(add(lit(1), lit(2)), lit(3)), lit(5));

void pptree(Tree t) {
  str nodeLabel(value v) {

    if (appl(prod(lex(str x), _, _), _) := v) {
        return "<x>";
    }

    if (appl(regular(_), _) := v) {
        return "[]";
    }

    if (appl(prod(label(str l, sort(str nt)), _, _), _) := v) {
        return "<l>:<nt>";
    }
    if (appl(prod(sort(str nt), _, _), _) := v) {
        return "<nt>";
    }
    if (appl(prod(lit(str x), _, _), _) := v) {
        return "\"<x>\"";
    }

  
    if (amb(_) := v) {
        return "🔶";
    }
    return "<v>";
  }

  lrel[str,value] edges(value v) {
    if (appl(prod(lit(str x), _, _), _) := v) {
        return [];
    }

    if (appl(prod(lex(_), _, _), _) := v) {
        return [<"", "<v>">];
    }

    if (appl(_,  list[Tree] args) := v) {
        return [<"", k> | Tree k <- args[0,2..]];
    }
    
    if (amb(set[Tree] alts) := v) {
        return [<"", a> | Tree a <- alts ];
    }
    return [];
  }

  return ppvalue(t, nodeLabel, edges);
}

void ppnode(node n) {
  str nodeLabel(value v) {
    if (list[value] _ := v) {
        return "[]";
    }
    if (set[value] _ := v) {
        return "{}";
    }
    if (map[value, value] _ := v) {
        return "()";
    }

    if (node k := v) {
        return getName(k);
    }
    return "<v>";
  }

  lrel[str,value] edges(value v) {
    if (list[value] l := v) {
        return [ <"", x> | value x <- l ];
    }
    if (set[value] s := v) {
        return [ <"", x> | value x <- s ];
    }
    if (map[value, value] m := v) {
        return [ <"<x>", m[x]> | value x <- l ];
    }
    if (node k := v) {
        return [ <"", kid> | value kid <- getChildren(k) ];
    }
    return [];
  }

  return ppvalue(n, nodeLabel, edges);
}

void ppvalue(value e, str(value) nodeLabel, lrel[str,value](value) edges) {
  println(nodeLabel(e));
  ppvalue_(e, nodeLabel, edges);
}

void ppvalue_(value e, str(value) nodeLabel, lrel[str,value](value) edges, str indent = "") {
  lrel[str,value] kids = edges(e);
  int i = 0;

  str indented(str last, str other) 
    = "<indent> <i == size(kids) - 1 ? last : other> ";
    
  for (<str l, value sub> <- kids) {
    println("<indented("└─", "├─")><l != "" ? "\u001b[34m─<l>→\u001b[0m ": ""><nodeLabel(sub)>");
    ppvalue_(sub, nodeLabel, edges, indent = indented(" ", "│"));
    i += 1;
  }
}
