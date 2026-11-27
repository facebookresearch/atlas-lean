# Immerman: FO(DTC) captures deterministic logspace on ordered structures

On canonically ordered finite structures, a query is definable in FO(DTC) if and only if it is decidable in deterministic logarithmic space $\mathrm{L}$. Moreover every FO(DTC)-definable ordered query is FO(TC)-definable, consistent with $\mathrm{L} \subseteq \mathrm{NL}$, and the problem of deciding reachability in graphs of out-degree at most one is complete for FO(DTC) under first-order reductions.

## Proof sketch

A logspace machine's configurations are tuples of elements; its deterministic step relation is first-order definable, and acceptance is a deterministic reachability, an FO(DTC) formula. Conversely a logspace algorithm evaluates DTC by following unique successors with a counter, and first-order connectives and quantifiers by iteration.

## Depends on

- [First-order logic with deterministic transitive closure](first-order-logic-deterministic-transitive-closure.md)
- [Canonically ordered structures with BIT](../ordered-structures-and-arithmetic/canonically-ordered-structures-with-bit.md)
- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)
- [Ordered first-order interpretations and first-order queries](../ordered-structures-and-arithmetic/ordered-first-order-interpretations.md)

## Proof depends on

- [Immerman: FO + transitive closure is NL on ordered structures](../transitive-closure-logic-and-nl/fo-tc-eq-nl.md)
- [Full-tuple interpretations pull back FO(LFP), FO(TC) and SO∃-Horn sentences](../ordered-structures-and-arithmetic/full-tuple-interpretations-preserve-logics.md)
- [First-order model checking for a fixed sentence is in L](../logical-characterizations-of-l-nl-p-np/first-order-queries-in-logspace.md)

## Sources

- N. Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 760–778, 1987, Theorem 4.2.
- N. Immerman, Descriptive Complexity, Springer, 1999.
