# The exponents s_k of k-SAT and #k-SAT

For $k\ge1$, the **SAT exponent** $s_k$ is the infimum of $\delta\ge0$ such that $k$-SAT on $n$ variables is decidable by a deterministic algorithm in time $2^{\delta n}\cdot\mathrm{poly}(L)$, where $L$ is the encoded length; $s^{\#}_k$ is the analogous exponent for computing the number of satisfying assignments. Exhaustive search gives $0\le s_k\le s^{\#}_k\le1$, and both are nondecreasing in $k$. In these terms $\mathrm{ETH}\iff s_3>0$ and $\mathrm{SETH}\iff\lim_{k\to\infty}s_k=1$; the counting version $\#\mathrm{ETH}$ states that some constant $c>0$ admits no deterministic algorithm computing $\#3$-SAT in time $\exp(c\cdot n)$. Randomized versions ($\mathrm{rETH}$, $\mathrm{rSETH}$) use bounded-error algorithms.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [The 3SAT decision problem](../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)
- [Counting satisfying assignments of a CNF formula](../../counting-complexity/counting-satisfiability-sat/count-sat-fun.md)

## Sources

- Russell Impagliazzo and Ramamohan Paturi, "On the Complexity of k-SAT", Journal of Computer and System Sciences 62(2), 2001.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Conjectures 14.1 and 14.2.
- Holger Dell, Thore Husfeldt, Dániel Marx, Nina Taslaman and Martin Wahlén, "Exponential Time Complexity of the Permanent and the Tutte Polynomial", ACM Transactions on Algorithms 10(4), 2014, Section 1 (the counting hypothesis #ETH).
