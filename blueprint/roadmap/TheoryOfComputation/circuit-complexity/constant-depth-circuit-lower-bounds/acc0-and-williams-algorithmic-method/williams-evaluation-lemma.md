# Williams's evaluation lemma for SYM ∘ AND circuits

A $\mathrm{SYM}\circ\mathrm{AND}$ circuit with $s\le 2^{0.1n}$ AND gates on $n$ inputs, whose symmetric gate can be evaluated in time $\mathrm{poly}(s)$, can be evaluated on all $2^n$ inputs in total time $(2^n+\mathrm{poly}(s))\cdot\mathrm{poly}(n)$, producing its whole truth table (on a multi-tape Turing machine or any other standard model).

## Proof sketch

Let $c(S)$ be the number of AND gates reading exactly $S$. The number of gates satisfied by the input with support $T$ is the zeta transform $\sum_{S\subseteq T}c(S)$, computed for all $T$ by Yates's dynamic programming in $O(2^n n)$ arithmetic operations; then tabulate the symmetric function on $0,\dots,s$ once, in $\mathrm{poly}(s)$ time, and look up each value.

## Depends on

- [SYM ∘ AND circuits](sym-and-circuits.md)
- [Deterministic time classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](../../../../ComputerScience/algebraic-and-numerical-algorithms/fast-zeta-transform-and-subset-convolution/yates-algorithm.md)

## Sources

- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014 (Lemma 4.2, Proof 1).
- Andreas Björklund, Thore Husfeldt, Mikko Koivisto, "Set Partitioning via Inclusion–Exclusion", SIAM Journal on Computing 39(2), 2009.
