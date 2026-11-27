# The matrix product operator threshold problem is undecidable

No algorithm decides, given a translation-invariant matrix product operator with open boundary conditions and a threshold $\lambda$, whether adding $\lambda$ times the identity leaves it positive semidefinite for every system size. This holds for every fixed rational threshold, already with physical dimension 2, bond dimension 42 and diagonal local matrices.

**Problem.** An instance is given by MPO tensors $M \in \mathbb{Q}^{d \times d \times D \times D}$ and boundary vectors $\lvert L\rangle, \lvert R\rangle \in \mathbb{Q}^{D}$, with rational entries, which define the operators $\rho(L, M, R, n)$ of a [translation-invariant matrix product operator](translation-invariant-matrix-product-operators.md). The *MPO threshold problem* with threshold $\lambda$ asks: is there a system size $n \geq 1$ such that $\rho(L, M, R, n) + \lambda \mathbb{1}$ is not positive semidefinite?

**Theorem (Kliesch, Gross and Eisert).** For every rational number $\lambda$ the MPO threshold problem with threshold $\lambda$ is undecidable (Theorem 5 of the source). This remains true when the physical dimension is $d = 2$, the bond dimension is $D = 42$ and every local matrix $M_{i,j}$ is diagonal.

With the system size $n$ part of the input instead, the bounded problem is NP-hard for every rational threshold and every physical dimension $d \geq 2$ (Theorem 4 of the source). With diagonal local matrices, $\rho(L, M, R, n)$ is diagonal in the product basis, so the question is whether some word gives a negative enough diagonal entry.

## Depends on

- [Translation-invariant matrix product operators](translation-invariant-matrix-product-operators.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem with seven pairs of binary words, which the source quotes as undecidable (Matiyasevich and Sénizergues). Given pairs $(u_\alpha, v_\alpha)_{\alpha \in [d]}$ and the threshold $\lambda$, Lemma 11 builds boundary vectors and nonnegative integer $6 \times 6$ matrices $A^{(1)}, \dots, A^{(d)}$ with

$$
\langle L \rvert A^{(w_1)} \cdots A^{(w_n)} \lvert R\rangle = -(\lambda + 1) \text{ if } U(w) = V(w), \qquad \langle L \rvert A^{(w_1)} \cdots A^{(w_n)} \lvert R\rangle \geq -\lambda \text{ otherwise},
$$

for every word $w$, where $U(w) = u_{w_1} \cdots u_{w_n}$ and $V(w) = v_{w_1} \cdots v_{w_n}$. Lemma 12, from Blondel and Tsitsiklis, re-encodes the $d$ matrices as two matrices of size $6d$ through an injective morphism of word monoids, which lowers the physical dimension to 2. Placing the resulting matrices on the diagonal of the MPO tensor, $M^{(\alpha,\beta)} = \sum_\gamma \delta_{\alpha\gamma}\delta_{\beta\gamma} C^{(\gamma)}$, makes the diagonal entries of $\rho(L, M, R, n) + \lambda\mathbb{1}$ equal to $-1$ on words that solve the instance and nonnegative otherwise. So the operator fails to be positive for some $n$ exactly when the instance has a solution.

## Sources

- M. Kliesch, D. Gross and J. Eisert, "Matrix-product operators and states: NP-hardness and undecidability", *Physical Review Letters* 113(16), 160503, 2014, doi:[10.1103/PhysRevLett.113.160503](https://doi.org/10.1103/PhysRevLett.113.160503). Numbering of the version read, arXiv:1404.4466v2: Problem 3 (the MPO threshold problem), Theorem 5 (undecidability), Theorem 4 (NP-hardness of the bounded problem), Lemmas 11 and 12 and the proof of Theorems 4 and 5.
