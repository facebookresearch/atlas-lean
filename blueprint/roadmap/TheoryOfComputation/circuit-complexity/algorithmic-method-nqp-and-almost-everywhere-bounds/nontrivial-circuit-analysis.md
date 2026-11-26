# Non-trivial satisfiability and derandomization algorithms for a circuit class

Let $\mathcal{C}$ be a circuit class closed under projections. A **non-trivial $\mathcal{C}$-SAT algorithm** decides, given a $\mathcal{C}$-circuit $C$ on $n$ inputs and of size $s$, whether $C$ is satisfiable, in time

$$
\frac{2^n}{n^{\omega(1)}} \cdot \operatorname{poly}(s), \qquad \text{for all } s \le 2^{n^{o(1)}} \ (\text{or } s = \operatorname{poly}(n)).
$$

A **non-trivial derandomization** (Gap-UNSAT or CAPP algorithm) for $\mathcal{C}$ distinguishes, deterministically in the same time, circuits that are unsatisfiable from circuits with at least $2^{n-1}$ satisfying assignments. Every non-trivial SAT algorithm is a non-trivial derandomization algorithm.

## Depends on

- [Williams: NEXP is not contained in ACC0](../williams-nexp-not-in-acc0.md)

## Sources

- R. Williams, "Improving exhaustive search implies superpolynomial lower bounds", SIAM Journal on Computing 42 (2013) 1218-1244; STOC (2010).
- R. Williams, "Nonuniform ACC circuit lower bounds", Journal of the ACM 61 (2014).
- L. Chen, X. Lyu, R. Williams, "Almost-everywhere circuit lower bounds from non-trivial derandomization", FOCS (2020), ECCC TR20-150.
