# Edit distance has no strongly subquadratic algorithm unless SETH fails

If for some $\delta > 0$ the edit distance of two strings of length $n$ over a fixed alphabet of seven symbols, the alphabet of the reduction, can be computed in time $O(n^{2-\delta})$, then the Strong Exponential Time Hypothesis fails: there is $\varepsilon > 0$ such that, for every $k$, $k$-SAT on $N$ variables can be decided in time $O(2^{(1-\varepsilon)N})$. The proof reduces Orthogonal Vectors to edit distance by vector gadgets.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](exponential-time-hypothesis-and-strong.md)
- [Fine-grained reductions](fine-grained-reductions.md)

## Sources

- A. Backurs and P. Indyk, "Edit distance cannot be computed in strongly subquadratic time (unless SETH is false)", *Proceedings of the 47th ACM STOC*, 2015; *SIAM Journal on Computing* 47(3), 2018, <https://arxiv.org/abs/1412.0348>
