

## Proposal

Extend pattern syntax:

C[Pattern] := x
x matches context type C with hole matching Pattern.
typeOf c must be same as type of x.
C c[Pattern] := x binds c to a value of type x with special value "hole" (???)


C c:[Pattern] := x ==> compiles to ==>

C c:apply(..., Pattern (where hole is)...) := x;
 or ... or ... (for every possible ...)




Can be nested:

C[apply(Id, M[Expr e])] := x;

In value context:

C[Expr]
Plug expression in the hole of context value C, where typeof Expr is
type of hole of C.


Declare them as follows: 

```
context E[Expr] 
  = ☐
  | apply(plus1(), E)
  | apply(E, Expr)
  | apply(lambda(Id, E), Expr)
  | apply(lambda(Id, E[Id]), E)
  ;
```

But need to distinguish the top-level type from the hole type, so maybe:

```
context E[Expr] 
  = ☐
  | G // this one embeds another context type (a lone Expr is not allowed)
  | apply(plus1(), E)
  | apply(E, Expr)
  | apply(lambda(Id, E), Expr)
  | apply(lambda(Id, E[Id]), E)
  ;
```

Since all alts must be compatible to Expr, we can typecheck the alternatives
to use only constructors from Expr, and valid nestings.

Each alt should have exactly 1 recursion (except hole) to another context type.
Plugging a context type does not count as a context (basically E[X] turns context E into a typeOf(X)).


NB: since hole is an alt, we always require that E[Expr] ("E of Expr") also matches Expr. Is this enough? I think we can always refactor into more contexts when the need arises to have, e.g., Expr holes directly in Stmt contexts.




