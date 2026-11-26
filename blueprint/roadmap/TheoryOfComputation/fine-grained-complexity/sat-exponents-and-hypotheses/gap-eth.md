# Gap-ETH

For $0\le s< c\le1$, $\mathrm{Gap}\text{-}k\text{-SAT}_{c,s}$ is the promise problem of distinguishing $k$-CNFs in which a $c$ fraction of clauses can be satisfied (yes) from those in which at most an $s$ fraction can (no). The **Gap Exponential Time Hypothesis** states that for some $\varepsilon>0$ and $s<1$, $\mathrm{Gap}\text{-}3\text{-SAT}_{1,s}$ has no deterministic (resp. randomized, for rGap-ETH) algorithm in time $2^{o(n)}$. Exhaustive search solves every gap problem in time $2^{n}\mathrm{poly}$; Gap-ETH implies ETH.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](k-sat-exponents.md)
- [MAXIMUM SATISFIABILITY as a decision problem](../../np-completeness/satisfiability/maximum-satisfiability/max-sat-dec.md)
- [Promise problems and promise classes](../../randomized-and-quantum-complexity/promise-and-randomized-classes/promise-problems.md)

## Sources

- Irit Dinur, "Mildly Exponential Reduction from Gap 3SAT to Polynomial-Gap Label-Cover", Electronic Colloquium on Computational Complexity, report TR16-128, 2016.
- Pasin Manurangsi and Prasad Raghavendra, "A Birthday Repetition Theorem and Complexity of Approximating Dense CSPs", 44th International Colloquium on Automata, Languages, and Programming (ICALP 2017), 2017.
