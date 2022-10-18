module ParseE_Paren

import E_Paren;
import ParseTree;

E parse(loc l)
  = parse(#E, l, allowAmbiguity=true);

E parse(str src, loc l)
  = parse(#E, src, l, allowAmbiguity=true);