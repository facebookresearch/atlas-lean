# First-order model checking for a fixed sentence is in L

For every fixed first-order sentence $\varphi$ over a finite relational vocabulary (with or without the built-in order and BIT), the set of encoded finite structures satisfying $\varphi$ is decidable in deterministic logarithmic space; malformed encodings are rejected. Thus $\mathrm{FO}\subseteq\mathsf{L}$ (indeed $\subseteq\mathsf{AC}^0$ with BIT).

## Proof sketch

Evaluate $\varphi$ recursively: each quantifier ranges over the universe with an $O(\log n)$-bit counter, the quantifier depth is constant, and atomic formulas are looked up in the input truth tables at addresses computed from the counters.

## Depends on

- [Canonically ordered structures with BIT](../ordered-structures-and-arithmetic/canonically-ordered-structures-with-bit.md)
- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999, Theorem 3.1.
