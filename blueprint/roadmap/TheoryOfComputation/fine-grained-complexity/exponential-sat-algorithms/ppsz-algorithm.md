# PPSZ: the success probability with bounded-width implication

PPSZ strengthens PPZ: in the original algorithm the formula is first closed under $s$-bounded resolution (resolvents of clauses of width at most $s$ whose resolvent has width at most $s$), with $s=s(n)\to\infty$ slowly, before the PPZ rounds; Hertli's variant, which satisfies the same bounds, instead sets a variable during the round whenever its value is $s$-implied, i.e. implied by at most $s$ clauses. For every satisfiable $k$-CNF, $k\ge3$, one round succeeds with probability at least $2^{-(1-\mu_k/(k-1)+o(1))n}$, where $\mu_k=\sum_{j\ge1}\frac{1}{j(j+1/(k-1))}$; for $k=3$ this gives time $O(1.308^{n})$. Paturi, Pudlák, Saks and Zane prove this bound for uniquely satisfiable formulas when $k\ge3$ and for all satisfiable formulas when $k\ge5$ (their Theorem 1); Hertli proved it for all satisfiable $k$-CNFs, $k\ge3$.

## Proof sketch

For a unique solution, each variable $x$ has a critical clause tree of height $h$; placing variables at independent uniform times, $x$ is forced whenever the tree contains a 'cut' of earlier variables, which happens with probability at least $Q_k(h)$, the solution of a depth recursion converging to $\mu_k/(k-1)$. Hertli's argument extends the bound to arbitrary satisfiable formulas by a cost-redistribution over frozen and non-frozen variables.

## Depends on

- [Bounded-width implication (s-implication)](../../../ComputerScience/randomized-algorithms/exponential-time-k-sat-algorithms/bounded-width-implication.md)
- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Proof depends on

- [Satisfiability coding lemma: PPZ round success probability](../../../ComputerScience/randomized-algorithms/exponential-time-k-sat-algorithms/ppz-round-success-probability.md)

## Sources

- Ramamohan Paturi, Pavel Pudlák, Michael E. Saks and Francis Zane, "An Improved Exponential-Time Algorithm for k-SAT", Journal of the ACM 52(3), 2005, Theorem 1.
- Timon Hertli, "3-SAT Faster and Simpler – Unique-SAT Bounds for PPSZ Hold in General", 52nd Annual Symposium on Foundations of Computer Science (FOCS), 2011, Theorem 1 and Section 2 (s-implication).
- Dominik Scheder and John P. Steinberger, "PPSZ for General k-SAT – Making Hertli's Analysis Simpler and 3-SAT Faster", 32nd Computational Complexity Conference (CCC 2017), 2017.
