module paper::murebel::Plugin

import util::IDE;
import paper::murebel::Syntax;
import ParseTree;

void main() {
  registerLanguage("μRebel", "mrbl", start[Prog](str src, loc l) {
    return parse(#start[Prog], src, l);
  });
}