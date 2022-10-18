module lang::credex::demo::amb::Util

import ParseTree;

bool credexMatch(type[&T<:Tree] lang, str src) {
  try {
    parse(lang, src);
    return true;
  }
  catch ParseError(_): {
    return false;
  }
}