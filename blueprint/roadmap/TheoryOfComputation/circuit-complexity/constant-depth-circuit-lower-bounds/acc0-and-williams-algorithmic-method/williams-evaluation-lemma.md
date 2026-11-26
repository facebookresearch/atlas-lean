# Williams's evaluation lemma for SYM ∘ AND circuits

A $\mathrm{SYM}\circ\mathrm{AND}$ circuit with $s$ AND gates on $n$ inputs, whose symmetric gate can be evaluated in time $\mathrm{poly}(s)$, can be evaluated on all $2^n$ inputs in total time $(2^n+\mathrm{poly}(s))\cdot\mathrm{poly}(n)$ on a multi-tape Turing machine.

## Proof sketch

Let $c(S)$ be the number of AND gates reading exactly $S$. The number of gates satisfied by the input with support $T$ is the zeta transform $\sum_{S\subseteq T}c(S)$, computed for all $T$ by Yates's dynamic programming in $O(2^n n)$ arithmetic operations; then apply the symmetric gate to each value.

## Depends on

- [SYM ∘ AND circuits](sym-and-circuits.md)
- [Deterministic time classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM, 2014.
- Andreas Björklund, Thore Husfeldt, Mikko Koivisto, "Set Partitioning via Inclusion–Exclusion", SIAM Journal on Computing, 2009.
