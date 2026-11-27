# Sensitivity bounds the number of relevant coordinates

For every $f : \{0,1\}^n \to \{0,1\}$, the number of coordinates $i$ that are sensitive at some input is at most $s(f) \cdot 4^{s(f)}$. Consequently, if $n \ge 1$ and $f$ depends on all $n$ coordinates, then $\lceil \log_2 n \rceil \le 3\, s(f)$, so every function depending on all its variables has sensitivity $\Omega(\log n)$.

## Proof sketch

Simon's lemma: every coordinate that is sensitive somewhere has influence at least $2^{1 - 2s(f)}$, proved by induction on dimension within the subcube spanned by the at most $2s(f)$ coordinates sensitive at $x$ or at $x \oplus e_i$. Summing over relevant coordinates and using that total influence is average sensitivity, at most $s(f)$, bounds their number by $s(f) \cdot 2^{2s(f) - 1}$. Then $\log_2 n \le \log_2 s + 2s \le 3s$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- H.-U. Simon, "A Tight Ω(log log n)-Bound on the Time for Parallel RAM's to Compute Nondegenerated Boolean Functions", FCT 1983 (the bound on relevant variables in terms of sensitivity).
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
