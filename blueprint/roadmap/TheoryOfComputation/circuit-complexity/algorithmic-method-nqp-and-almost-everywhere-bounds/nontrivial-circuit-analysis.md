# Non-trivial satisfiability and derandomization algorithms for a circuit class

Let $\mathcal{C}$ be a circuit class closed under projections. For a size bound $s(n)$, with $s(n) = 2^{n^{o(1)}}$ or $s(n) = \operatorname{poly}(n)$, a **non-trivial $\mathcal{C}$-SAT algorithm** for size $s(n)$ decides, given a $\mathcal{C}$-circuit $C$ on $n$ inputs and of size at most $s(n)$, whether $C$ is satisfiable, in time

$$
\frac{2^n}{n^{\omega(1)}}.
$$

A **non-trivial derandomization** (Gap-UNSAT or CAPP algorithm) for $\mathcal{C}$ distinguishes, deterministically in the same time, circuits that are unsatisfiable from circuits with at least $2^{n-1}$ satisfying assignments. Every non-trivial SAT algorithm is a non-trivial derandomization algorithm.

## Sources

- R. Williams, "Improving exhaustive search implies superpolynomial lower bounds", SIAM Journal on Computing 42 (2013) 1218-1244; STOC (2010).
- R. Williams, "Nonuniform ACC circuit lower bounds", Journal of the ACM 61 (2014).
- L. Chen, X. Lyu, R. Williams, "Almost-everywhere circuit lower bounds from non-trivial derandomization", FOCS (2020), ECCC TR20-150.
