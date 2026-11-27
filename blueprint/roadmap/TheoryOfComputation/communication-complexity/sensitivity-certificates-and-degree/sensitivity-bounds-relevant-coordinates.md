# Sensitivity bounds the number of relevant coordinates

Say that $f : \{0,1\}^n \to \{0,1\}$ *depends on* the $i$-th variable if the $i$-th bit is sensitive for $f$ at some input, and let $n_0$ be the number of variables on which $f$ depends. Then

$$s(f) \cdot 4^{s(f)} \ge n_0,$$

and consequently, for $n_0 \ge 2$, $s(f) \ge \tfrac12 \log_2 n_0 - \tfrac12 \log_2 \log_2 n_0 + \tfrac12$. In particular every function depending on all $n$ of its variables has sensitivity $\Omega(\log n)$.

## Proof sketch

Simon's lemma: every coordinate that is sensitive somewhere has influence at least $2^{1 - 2s(f)}$, proved from the fact that a nonempty subgraph of the cube with minimum degree $\delta$ has at least $2^{\delta}$ vertices, applied to a component of inputs on which the coordinate stays sensitive, which has minimum degree at least $n - 2s(f) + 1$. Summing over relevant coordinates and using that total influence is average sensitivity, at most $s(f)$, bounds their number by $s(f) \cdot 2^{2s(f) - 1}$.

Derived here (not stated in the cited sources): if $n \ge 1$ and $f$ depends on all $n$ coordinates, then $\log_2 n \le \log_2 s(f) + 2s(f) \le 3s(f)$, so $\lceil \log_2 n \rceil \le 3\, s(f)$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- P. Hatami, R. Kulkarni and D. Pankratov, "Variations on the Sensitivity Conjecture", Theory of Computing Library, Graduate Surveys 4, 2011, Section 3, Theorem 3.1, Lemma 3.2 and Corollary 3.3 (both attributed to H.-U. Simon).
- H.-U. Simon, "A Tight Ω(log log n)-Bound on the Time for Parallel RAM's to Compute Nondegenerated Boolean Functions", FCT 1983 (the bound on relevant variables in terms of sensitivity).
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
