# Gap-ETH

For $0\le s< c\le1$, $\mathrm{Gap}\text{-}k\text{-SAT}_{c,s}$ is the promise problem of distinguishing $k$-CNFs in which a $c$ fraction of clauses can be satisfied (yes) from those in which at most an $s$ fraction can (no). The **Gap Exponential Time Hypothesis** states that there are constants $\varepsilon,\gamma>0$ such that no algorithm decides $\mathrm{Gap}\text{-}3\text{-SAT}_{1,1-\varepsilon}$ on formulas with $n$ variables in time $O(2^{\gamma n})$ (the deterministic version excludes deterministic algorithms, the randomized version rGap-ETH also bounded-error randomized ones). Dinur states it for formulas with at most $Dn$ clauses and $\varepsilon=0.1$; Manurangsi and Raghavendra measure $n$ in clauses and note that, by sparsification and by subsampling clauses, the variants are equivalent. Exhaustive search solves every gap problem in time $2^{n}\mathrm{poly}$; Gap-ETH implies ETH.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](k-sat-exponents.md)
- [MAXIMUM SATISFIABILITY as a decision problem](../../np-completeness/satisfiability/maximum-satisfiability/max-sat-dec.md)
- [Promise problems and promise classes](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/promise-and-randomized-classes/promise-problems.md)

## Sources

- Irit Dinur, "Mildly Exponential Reduction from Gap 3SAT to Polynomial-Gap Label-Cover", Electronic Colloquium on Computational Complexity, report TR16-128, 2016, Hypothesis 2.5.
- Pasin Manurangsi and Prasad Raghavendra, "A Birthday Repetition Theorem and Complexity of Approximating Dense CSPs", 44th International Colloquium on Automata, Languages, and Programming (ICALP 2017), 2017, Conjecture 2 (ETHA).
