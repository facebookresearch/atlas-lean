# Polynomial-space decider runs in exponential time

Let $M$ be a deterministic multi-tape Turing machine over the Boolean alphabet with finitely many
states that decides a language $L$ of bitstrings and runs in space $c_1 n^d + c_2$: on every input
of length $n$, every computation of $M$ visits at most $c_1 n^d + c_2$ work-tape cells. Then there
are natural numbers $D$, $A$ and $B$ such that $M$ runs in time $A \cdot 2^{n^D} + B$: on every input
of length $n$, every computation of $M$ with at least $A \cdot 2^{n^D} + B$ steps ends in a halted
configuration.

The machine halts on every input because it decides $L$; the space bound then limits the number of
distinct configurations a halting computation can pass through.
