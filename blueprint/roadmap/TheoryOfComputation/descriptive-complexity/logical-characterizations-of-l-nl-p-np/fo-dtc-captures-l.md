# Immerman: FO(DTC) captures L on ordered structures

On ordered finite structures (with $\le$, BIT, $0$, $1$, $\max$), a query is definable by an FO(DTC) sentence if and only if its encoded language is in deterministic logarithmic space: $\mathrm{FO(DTC)}=\mathsf{L}$.

## Proof sketch

FO(DTC) $\subseteq$ L: a deterministic closure is evaluated by following the unique outgoing edge for at most $n^{k}$ steps with a step counter, compiling nested closures into nested counter loops. L $\subseteq$ FO(DTC): configurations of a logspace machine are $k$-tuples, its deterministic step relation is first-order definable, and acceptance is deterministic reachability of the accepting configuration.

## Depends on

- [Deterministic transitive closure logic FO(DTC)](deterministic-transitive-closure-logic.md)
- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)

## Proof depends on

- [First-order model checking for a fixed sentence is in L](first-order-queries-in-logspace.md)
- [First-order interpretations, first-order reductions and quantifier-free projections](first-order-reductions.md)

## Sources

- Neil Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 1987, Theorem 4.2.
- Neil Immerman, "Descriptive Complexity", Springer, 1999.
