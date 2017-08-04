module paper::Plugin

import paper::Contextual;
import util::IDE;
import ParseTree;

void main() {
  registerLanguage("Contextual", "ctx", start[Contexts](str src, loc l) {
    return parse(#start[Contexts], src, l);
  });
}