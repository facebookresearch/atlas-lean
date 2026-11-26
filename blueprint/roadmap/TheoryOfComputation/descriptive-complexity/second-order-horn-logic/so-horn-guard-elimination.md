# Guard elimination for SO∃-Horn on successor structures

On canonically ordered structures with a primitive successor relation and the constants $0$ and $\max$, every SO∃-Horn sentence with arbitrary first-order guards is equivalent to an SO∃-Horn sentence whose guards are quantifier-free. For each subformula $\psi$ of a guard, auxiliary relation variables for $\psi$ and $\neg\psi$ are introduced whose least extensions are the tuples satisfying them, computed by Horn clauses that iterate quantifiers along the successor.

## Proof sketch

Universal and existential quantifiers over an ordered universe with successor are evaluated by Horn recursion from $0$ to $\max$; positive and negative versions are maintained simultaneously so that negations become Horn-expressible.

## Depends on

- [Existential second-order Horn logic](existential-second-order-horn-logic.md)
- [Canonically ordered structures with BIT](../ordered-structures-and-arithmetic/canonically-ordered-structures-with-bit.md)

## Sources

- E. Grädel, "Capturing Complexity Classes by Fragments of Second-Order Logic", Theoretical Computer Science 101(1), 35–57, 1992.
