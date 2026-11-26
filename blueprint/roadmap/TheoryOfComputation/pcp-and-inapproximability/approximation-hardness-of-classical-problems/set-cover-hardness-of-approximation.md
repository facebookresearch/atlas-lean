# Lund–Yannakakis–Feige: Set Cover is NP-hard to approximate within every constant

For every constant $c \ge 1$ the gap version of (unweighted) Set Cover is NP-hard: it is NP-hard to distinguish instances having a cover of size at most $k$ from instances in which every cover has size greater than $c k$. The reduction is from Label Cover with small soundness via partition gadgets: each edge $e = (u, w)$ receives $\deg(u)\deg(w)$ copies of a gadget universe, the set for (left vertex $u$, label $a$) covers $U \setminus S_{\pi_e(a)}$ in the gadgets of edges at $u$, and the set for (right vertex $w$, label $b$) covers $S_b$. With larger gadgets the same method gives hardness of $c \ln n$ for some $c > 0$ unless $\mathrm{NP} \subseteq \bigcup_{k \ge 1} \mathrm{DTIME}(n^{\log^{k} n})$ (Lund–Yannakakis) and of $(1 - \varepsilon) \ln n$ for every $\varepsilon > 0$ unless $\mathrm{NP} \subseteq \mathrm{DTIME}(n^{O(\log\log n)})$ (Feige), matching the greedy algorithm.

## Proof sketch

A satisfying labelling gives a cover of cost $2m$ after weighting. Conversely, a cover of cost $\rho \cdot 2m$ gives each vertex a list of chosen labels; if lists are short for an edge, the gadget's separation property forces a left label projecting onto a right label in the lists. Markov's inequality and a random choice from the lists yield a labelling satisfying a $(1 - 2\rho/t)\cdot 4/t^2$ fraction of edges, contradicting small soundness.

## Depends on

- [Label Cover (projection games)](../two-prover-games-and-parallel-repetition/label-cover-projection-games.md)
- [Partition gadget for Set Cover hardness](partition-gadget-for-set-cover.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Label Cover is NP-hard with perfect completeness and arbitrarily small soundness](../two-prover-games-and-parallel-repetition/label-cover-np-hard-with-small-soundness.md)
- [Small partition gadgets exist](small-partition-gadgets-exist.md)

## Sources

- C. Lund and M. Yannakakis, "On the Hardness of Approximating Minimization Problems", Journal of the ACM 41(5), 1994.
- U. Feige, "A Threshold of ln n for Approximating Set Cover", Journal of the ACM 45(4), 1998.
