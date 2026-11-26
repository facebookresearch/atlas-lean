# PPSZ: the success probability with bounded-width implication

PPSZ modifies PPZ by setting a variable whenever its value is implied by a set of at most $w$ clauses (w-implication), with $w=w(n)\to\infty$ slowly. For every satisfiable $k$-CNF, $k\ge3$, one round succeeds with probability at least $2^{-(1-\mu_k/(k-1)+o(1))n}$, where $\mu_k=\sum_{j\ge1}\frac{1}{j(j+1/(k-1))}$; for $k=3$ this gives time $O(1.308^{n})$. The bound holds first for formulas with an isolated (e.g. unique) solution via critical clause trees, and for all satisfiable formulas by Hertli's analysis.

## Proof sketch

For an $h$-isolated solution, each variable $x$ has a critical clause tree of height $h$; placing variables at independent uniform times, $x$ is forced whenever the tree contains a 'cut' of earlier variables, which happens with probability at least $Q_k(h)$, the solution of a depth recursion converging to $\mu_k/(k-1)$. Hertli's argument extends the bound to arbitrary satisfiable formulas by a cost-redistribution over frozen and non-frozen variables.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Proof depends on

- [Paturi–Pudlák–Zane: the satisfiability coding lemma and PPZ](ppz-algorithm.md)

## Sources

- Ramamohan Paturi, Pavel Pudlák, Michael E. Saks and Francis Zane, "An Improved Exponential-Time Algorithm for k-SAT", Journal of the ACM 52(3), 2005.
- Timon Hertli, "3-SAT Faster and Simpler – Unique-SAT Bounds for PPSZ Hold in General", 52nd Annual Symposium on Foundations of Computer Science (FOCS), 2011.
- Dominik Scheder and John P. Steinberger, "PPSZ for General k-SAT – Making Hertli's Analysis Simpler and 3-SAT Faster", 32nd Computational Complexity Conference (CCC 2017), 2017.
