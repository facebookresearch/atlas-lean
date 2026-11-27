# Dual-rail translation of De Morgan circuits into monotone circuits

Every De Morgan circuit $C$ with $s$ gates on inputs $x_1,\dots,x_n$ is simulated by a monotone circuit $C^{\pm}$ with at most $2s$ AND/OR gates on the $2n+2$ inputs $0,1,x_1,\neg x_1,\dots,x_n,\neg x_n$ that computes, for every wire $w$ of $C$, both $w$ and $\neg w$: an AND gate becomes the AND of the positive rails and the OR of the negative rails, an OR gate dually, a NOT gate swaps rails at no cost, and a constant gate becomes the constant inputs $c$ and $\neg c$ at no cost. In particular monotone circuit size with free negative literals and constants is at most twice De Morgan size.

## Proof sketch

De Morgan's laws: $\neg(a\wedge b)=\neg a\vee\neg b$ and $\neg(a\vee b)=\neg a\wedge\neg b$; induct along the gates.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Sources

- Leslie M. Goldschlager, "The Monotone and Planar Circuit Value Problems Are Log Space Complete for P", ACM SIGACT News 9(2), 1977.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
