# Barrington's theorem: width-5 programs capture NC1

Every De Morgan formula of depth $d$ (negations free) is $\sigma$-computed, for every $5$-cycle $\sigma\in S_5$, by an $S_5$-program of length at most $4^d$. Consequently a language is in nonuniform $\mathsf{NC}^1$ if and only if its slices are computed by polynomial-length permutation branching programs of width $5$.

## Proof sketch

Induction on the formula. A variable is one instruction; negation takes a program that $\sigma^{-1}$-computes the argument and multiplies both group elements of its last instruction on the right by $\sigma$, so the product is $e$ when the argument is true and $\sigma$ when it is false and the length does not change; for a conjunction write $\sigma=\alpha\beta\alpha^{-1}\beta^{-1}$ as a commutator of two $5$-cycles, and concatenate programs for the two arguments computing $\alpha,\beta,\alpha^{-1},\beta^{-1}$, which multiplies the length by four; a $\tau$-computing program for any other $5$-cycle $\tau=\pi\sigma\pi^{-1}$ is obtained by conjugating every instruction by $\pi$, again without changing the length. Disjunctions are handled as negated conjunctions of negations. Conversely a width-$5$ program of polynomial length is evaluated by a balanced product tree of logarithmic depth.

## Depends on

- [Permutation branching programs of bounded width](permutation-branching-programs.md)
- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)

## Proof depends on

- [NC1 equals logarithmic formula depth and polynomial formula size](../circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-depth-and-karchmer-wigderson-games/nc1-equals-polynomial-size-formulas.md)

## Sources

- David A. Barrington, "Bounded-width polynomial-size branching programs recognize exactly those languages in NC^1", Journal of Computer and System Sciences, 1989.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
