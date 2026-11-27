# Consistency of a finite set of GPT transformations is undecidable

No algorithm decides whether a given finite set of rational normalization-preserving linear maps can be added as transformations to some generalized probabilistic theory without producing negative probabilities.

**Theorem (Massar).** Fix a rational unit effect $u$. The following problem is undecidable: given a finite set $\mathcal{T}_0 = \{T_1, \dots, T_K\}$ of rational $(d+1) \times (d+1)$ matrices with $u^\top T_i = u^\top$ for every $i$, decide whether $\mathcal{T}_0$ is [consistent](generalized-probabilistic-theories.md), that is, whether some single-party GPT $(\mathcal{S}_0, \mathcal{E}_0)$ with full-dimensional state and effect spaces makes $(\mathcal{S}_0, \mathcal{E}_0, \mathcal{T}_0)$ consistent (Theorem 3 of the source).

The source remarks that if unboundedness of matrix products is undecidable for $k$ matrices of dimension $d$, the theorem holds already for $K = k + 1$ transformations on $\mathbb{R}^{d+1}$. It also proves that, given in addition a finitely described single-party GPT $(\mathcal{S}_0, \mathcal{E}_0)$ and promised that $\mathcal{T}_0$ is consistent, it is undecidable whether the triple $(\mathcal{S}_0, \mathcal{E}_0, \mathcal{T}_0)$ is consistent (Theorem 4), and it proves analogous statements for translation-invariant multipartite theories (Theorems 5 and 6).

## Depends on

- [Generalized probabilistic theories and consistency of transformations](generalized-probabilistic-theories.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)

## Expansion

Given rational $d \times d$ matrices $M_1, \dots, M_k$, the proof places them in the lower-right blocks of candidate transformations on $\mathbb{R}^{d+1}$, with $u = (1, 0, \dots, 0)^\top$, and adds one more transformation. If all products $M_w$ are bounded, sufficiently small hypersphere state and effect spaces keep every probability $e^\top T_w \omega$ non-negative. If the products are unbounded, every full-dimensional state and effect space contains small balls, and a long enough product drives some probability negative. So consistency of $\mathcal{T}_0$ is equivalent to boundedness of the products, which is undecidable (Blondel and Tsitsiklis, by a reduction from strict emptiness of probabilistic automata, which keeps the dimension and adds one matrix). A complete expansion links the undecidability of boundedness of all products of a finite set of rational matrices (Theorem 2 of the source; Vincent D. Blondel and John N. Tsitsiklis, "The boundedness of all products of a pair of matrices is undecidable", *Systems and Control Letters* 41(2):135–140, 2000, doi:[10.1016/S0167-6911(00)00049-9](https://doi.org/10.1016/S0167-6911(00)00049-9)), which has no page on main.

## Sources

- Serge Massar, "Undecidability of consistency of generalized probabilistic theories", *Physical Review A* 114(4):042201, 2026, doi:[10.1103/42zl-6wmw](https://doi.org/10.1103/42zl-6wmw). Numbering of the version read, arXiv:2603.07002v4: Theorem 3, Theorem 4, Theorems 5 and 6, Theorem 2 and Section IV.B.
