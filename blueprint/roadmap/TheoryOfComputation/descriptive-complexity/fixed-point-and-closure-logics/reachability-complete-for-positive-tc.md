# Reachability is complete for positive transitive closure logic

On canonically ordered structures, the query REACH (is $\max$ reachable from $0$ in the directed graph $E$) is definable by an FO(TC) sentence in which the closure occurs positively, and every query definable in FO(positive TC) first-order reduces to REACH. Consequently, every query first-order reducible to REACH is FO(TC)-definable.

## Proof sketch

Definability is the single closure $[\mathrm{tc}\, E](0, \max)$. Conversely a positive-TC sentence can be put in the normal form of a single closure over tuples of a first-order step relation, which a first-order interpretation turns into an instance of REACH; this normal form comes from Immerman's proof that FO(TC) captures NL. Pulling the defining sentence of REACH back along a first-order reduction gives the consequence.

## Depends on

- [Formulas of first-order logic with transitive closure](../transitive-closure-logic-and-nl/tcfo.md)
- [Ordered first-order interpretations and first-order queries](../ordered-structures-and-arithmetic/ordered-first-order-interpretations.md)

## Proof depends on

- [Immerman: FO + transitive closure is NL on ordered structures](../transitive-closure-logic-and-nl/fo-tc-eq-nl.md)
- [Full-tuple interpretations pull back FO(LFP), FO(TC) and SO∃-Horn sentences](../ordered-structures-and-arithmetic/full-tuple-interpretations-preserve-logics.md)

## Sources

- N. Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 760–778, 1987: Theorem 3.1, Theorem 3.3 (normal form) and Corollary 3.6 (GAP is complete for NL via first-order translations).
- N. Immerman, Descriptive Complexity, Springer, 1999.
