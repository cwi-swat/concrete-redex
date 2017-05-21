module paper::r5rs::Util

import paper::r5rs::Syntax;
import String;
import List;

bool allValue(Expr* es)
  = ( true | it && (Expr)`<Value _>` := e | e <- es );

bool allNum(Expr* es)
  = ( true | it && (Expr)`<Num _>` := e | e <- es );
  
int toInt(Num n) = toInt("<n>");

list[int] ptrs(Store s) 
  = [ toInt(sf.key.n) | SF sf <- s.entries, sf.key has n ]; 

Num newPtr(Store s) {
  ps = ptrs(s);
  if (ps == []) {
    return 0;
  }
  return [Num]"<max(ps) + 1>";
}  

Key freshPP(Store s) = (Key)`.<Num n>`
  when Num n := newPtr(s); 

Key freshCP(Store s) = (Key)`λ<Num n>`
  when Num n := newPtr(s); 

Key freshMP(Store s) = (Key)`μ<Num n>`
  when Num n := newPtr(s); 

Store add(Id x, Value v, Store s)
  = add((Key)`<Id x>`, (Stored)`<Value v>`, s);
  
Store add(Key k, Stored s, (Store)`<{SF ","}* sfs>`)
  = (Store)`<{SF ","}* sfs>, <Key k> ↦ <Stored s>`;

set[Id] dom(Store s) = { x | SF sf <- s.entries, (Key)`<Id x>` := sf.key };  

Stored lookup(Key k, (Store)`<{SF ","}* _>, <Key x> ↦ <Stored v>, <{SF ","}* _>`) = v
  when k == x;

Stored lookup(Id x, Store s) = lookup((Key)`<Id x>`, s);
Stored lookup(PP x, Store s) = lookup((Key)`<PP x>`, s);
Stored lookup(CP x, Store s) = lookup((Key)`<CP x>`, s);
Stored lookup(MP x, Store s) = lookup((Key)`<MP x>`, s);
  
Store update(Id x, Value v, Store s)
  = update((Key)`<Id x>`, (Stored)`<Value v>`, s);

Store update(Key k, Stored s,  (Store)`<{SF ","}* v1>, <Key x> ↦ <Stored _>, <{SF ","}* v2>`)
  = (Store)`<{SF ","}* v1>, <Key k> ↦ <Stored s>, <{SF ","}* v2>`
  when x == k;
 
 
bool isValue(Expr e) = (Expr)`<Value _>` := e;
 
bool allValue(Expr* es) = ( true | it && isValue(e) | Expr e <- es );
