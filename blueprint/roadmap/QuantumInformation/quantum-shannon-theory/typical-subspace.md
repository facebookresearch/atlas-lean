# Typical subspace

Let $\rho$ be a density operator on a finite-dimensional space with eigenvalues $p_1, \dots, p_d$ and von Neumann entropy $S(\rho)$
(base-2 logarithm), and let $\delta > 0$. For $n \ge 1$, let $\Pi_n$ be the projector onto the span of the eigenvectors of
$\rho^{\otimes n}$ whose eigenvalue strings $(i_1, \dots, i_n)$ have $p_{i_j} > 0$ for all $j$ and
$\lvert -\frac1n \log_2 (p_{i_1} \cdots p_{i_n}) - S(\rho) \rvert \le \delta$. Then $\mathrm{Tr}(\Pi_n \rho^{\otimes n}) \to 1$ as
$n \to \infty$ and $\mathrm{rank}(\Pi_n) \le 2^{n(S(\rho) + \delta)}$ for every $n$.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under
the dependency sections.

- Statement prerequisite: Von Neumann entropy.

## Proof depends on

- [AEP and typical sets (finite iid)](../../InformationTheory/source-coding/remaining-clauses-of-aep-and-typical-sets.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Definition 5.41,
  Propositions 5.42 and 5.43, and the proof of Theorem 5.44, (5.224), (5.225) and (5.233). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019), Definitions 15.1.2 and 15.1.3 and
  Properties 15.1.1 and 15.1.2. <https://arxiv.org/pdf/1106.1445v8.pdf>
