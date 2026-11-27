# The Cook–Levin reduction is parsimonious

For every polynomial-time verifier $V$ with certificates of length $p(n)$, the Cook–Levin tableau formula $\varphi_x$ produced for an input $x$ has exactly as many satisfying assignments as there are certificates $w\in\{0,1\}^{p(|x|)}$ with $V(x,w)=1$. Consequently $\#\mathrm{SAT}$ is $\#\mathsf{P}$-complete under parsimonious reductions.

## Proof sketch

Every tableau variable other than the certificate bits is determined by the deterministic run of $V$ on $(x,w)$, so satisfying assignments are in bijection with accepted certificates.

## Depends on

- [Counting satisfying assignments of a CNF formula](../counting-satisfiability-sat/count-sat-fun.md)
- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Leslie G. Valiant, "The Complexity of Enumeration and Reliability Problems", SIAM Journal on Computing 8(3), 1979, Fact 1.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 6.18 and the corollaries after it.
