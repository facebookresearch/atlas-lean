# Schöning's random-walk algorithm for k-SAT

Consider one trial: choose a uniformly random assignment of the $n$ variables and, for $3n$ steps, stop if the formula is satisfied, otherwise pick an unsatisfied clause (deterministically) and flip a uniformly random one of its at most $k$ literals' variables. For every satisfiable $k$-CNF ($k\ge3$) a trial succeeds with probability at least

$$
\Bigl(\tfrac{k-1}{k}\Bigr)^{k-3}\Bigl(\tfrac{k}{2(k-1)}\Bigr)^{n}\Big/(3n+1),
$$

in particular at least $(3/4)^{n}/(3n+1)$ for $k=3$. Repeating $O\bigl((2(k-1)/k)^{n}\,\mathrm{poly}(n)\bigr)$ trials gives a bounded-error algorithm, implementable on fair-coin multi-tape machines in time $(2(k-1)/k)^{n}\mathrm{poly}(L)$ and polynomial space.

## Proof sketch

The Hamming distance to a fixed solution decreases with probability $\ge1/k$ at each step, so it dominates a biased random walk. Starting at distance $d$, the probability of reaching $0$ within $3d$ steps is at least $\binom{3d}{d}\frac{1}{3d+1}(1/k)^{2d}(1-1/k)^{d}\ge\frac{1}{3d+1}(k-1)^{-d}$ up to the stated constant, and averaging over the binomially distributed $d$ gives the bound.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Sources

- Uwe Schöning, "A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems", 40th Annual Symposium on Foundations of Computer Science (FOCS), 1999.
