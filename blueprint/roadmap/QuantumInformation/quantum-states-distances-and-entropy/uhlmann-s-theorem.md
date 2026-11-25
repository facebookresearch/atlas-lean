# Uhlmann's theorem

Let $\rho, \sigma$ be density operators on $\mathcal{X}$ and let $\mathcal{Y}$ be a space with
$\dim\mathcal{Y} \ge \max(\operatorname{rank}\rho, \operatorname{rank}\sigma)$. For every purification
$u \in \mathcal{X} \otimes \mathcal{Y}$ of $\rho$,

$$F(\rho, \sigma) = \max\{ |\langle u, v\rangle| : v \in \mathcal{X} \otimes \mathcal{Y} \text{ a purification of } \sigma\}.$$


## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Fidelity of quantum states.
- Proof prerequisite: Purification and unitary equivalence of purifications.
- Proof prerequisite: the trace-norm identity $\|X\|_1 = \max_U |\langle U, X\rangle|$ over unitary $U$, and the
  unitary invariance of the trace norm.
- Proof prerequisite: the identity $F(AA^*, BB^*) = \|A^*B\|_1$, proved from a polar decomposition of the block
  operator $\begin{pmatrix} 0 & A \\ 0 & 0 \end{pmatrix}$ (Watrous, Lemma 3.21); the polar decomposition below is
  applied to the adjoint to obtain the form $PU$ with $P$ positive semidefinite on the left.

## Proof depends on

- [Polar decomposition of a complex square matrix](../../LinearAlgebra/matrix-decompositions/polar-decomposition/polar-decomposition-theorem/exists-unitary-group-pos-semidef.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Theorem 3.22. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 9.2.1. <https://arxiv.org/pdf/1106.1445v8>
