# SETH implies the Orthogonal Vectors hypothesis

If the Strong Exponential Time Hypothesis holds, then for every $\varepsilon > 0$ there is $c > 0$ such that Orthogonal Vectors on $n$ vectors in $\{0,1\}^{c \log n}$ has no $O(n^{2-\varepsilon})$-time algorithm. The proof splits the variables of a CNF formula into two halves, lists the partial assignments of each half as vectors indexed by the clauses, and uses the sparsification lemma to reduce the number of clauses to linear.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](exponential-time-hypothesis-and-strong.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Fine-grained reductions](fine-grained-reductions.md)

## Sources

- Original reduction: R. Williams, "A new algorithm for optimal 2-constraint satisfaction and its implications", *Theoretical Computer Science* 348(2–3):357–365, 2005. The formulation follows Vassilevska Williams, the section on Orthogonal Vectors, which credits the reduction to R. Williams.
- V. Vassilevska Williams, "On some fine-grained questions in algorithms and complexity", *Proceedings of the ICM 2018*, <http://people.csail.mit.edu/virgi/eccentri.pdf>
