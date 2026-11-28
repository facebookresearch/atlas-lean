# The matrix product operator threshold problem is undecidable

No algorithm decides, given a translation-invariant matrix product operator with open boundary conditions and rational entries, whether adding a fixed rational multiple $\lambda$ of the identity leaves it positive semidefinite for every system size. This holds for every rational threshold, already with diagonal local matrices.

**Problem.** An instance is given by MPO tensors $M \in \mathbb{Q}^{d \times d \times D \times D}$ and boundary vectors $\lvert L\rangle, \lvert R\rangle \in \mathbb{Q}^{D}$, with rational entries, which define the operators $\rho(L, M, R, n)$ of a [translation-invariant matrix product operator with open boundary conditions](translation-invariant-matrix-product-operators.md). The *MPO threshold problem* with threshold $\lambda \in \mathbb{Q}$ asks: is there a system size $n \geq 1$ such that $\rho(L, M, R, n) + \lambda \mathbb{1}$ is not positive semidefinite?

**Theorem (Kliesch, Gross and Eisert).** For every rational number $\lambda$ the MPO threshold problem with threshold $\lambda$ is undecidable (Theorem 5 of the source). This remains true when every local matrix $M_{i,j}$ is diagonal.

The source states Theorem 5 in particular for physical dimension $d = 2$, bond dimension $D = 42$ and diagonal local matrices. Its proof of that case passes through Lemma 12, whose identity $\langle \tilde{L} \rvert B^{(X(w))} \lvert \tilde{R}\rangle = \langle L \rvert A^{(w)} \lvert R\rangle$ holds only for the words $X(w)$ in the image of the encoding; for other words over $\{1, 2\}$, such as $2^{d}$, it gives entries outside the two cases of Lemma 11, so that case is not established by the proof as written. The undecidability above follows from Lemma 11 alone (see below), with physical dimension equal to the number of pairs of the Post correspondence instance and bond dimension 6.

The bounded problem is the following: given the instance and a system size $n$, is $\rho(L, M, R, n) + \lambda \mathbb{1}$ positive semidefinite? It is NP-hard for every rational threshold and every physical dimension $d \geq 2$ (Problem 2 and Theorem 4 of the source). With diagonal local matrices, $\rho(L, M, R, n)$ is diagonal in the product basis, and the answer to the bounded problem is no exactly when some diagonal entry of $\rho(L, M, R, n) + \lambda \mathbb{1}$ is negative.

## Depends on

- [Translation-invariant matrix product operators with open boundary conditions](translation-invariant-matrix-product-operators.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

A good expansion links Lemma 11 of the source as its own result. The proof reduces the Post correspondence problem: given pairs $(u_\alpha, v_\alpha)_{\alpha \in [d]}$ of words over an alphabet $\Sigma$ of size $b$ and the threshold $\lambda$, write $\sigma(w) = \sum_{j=1}^{\lvert w\rvert} \sigma_\Sigma(w_j)\, b^{\lvert w\rvert - j}$ for the numeric value of a word, with digits $\sigma_\Sigma(a) \in [b]$, so that $\sigma$ is injective. Lemma 11 gives nonnegative integer $6 \times 6$ matrices $A^{(1)}, \dots, A^{(d)}$ and boundary vectors $\lvert L\rangle = \lvert 6\rangle$, $\lvert R\rangle = \lvert 1\rangle - \lvert 2\rangle + \lvert 3\rangle - (\lambda + 1)\lvert 6\rangle$ with

$$
\langle L \rvert A^{(w_1)} \cdots A^{(w_n)} \lvert R\rangle = \bigl(\sigma(U(w)) - \sigma(V(w))\bigr)^2 - (\lambda + 1)
$$

for every word $w$ over $[d]$, where $U(w) = u_{w_1} \cdots u_{w_n}$ and $V(w) = v_{w_1} \cdots v_{w_n}$ (Equation (C5) of the source). Placing these matrices on the diagonal of the MPO tensor, $M^{(\alpha,\beta)} = \delta_{\alpha\beta} A^{(\alpha)}$, makes $\rho(L, M, R, n)$ diagonal with entry $\langle L \rvert A^{(w)} \lvert R\rangle$ at the basis vector $\lvert w_1 \cdots w_n\rangle$. Every word over $[d]$ is a basis label, so the diagonal entries of $\rho(L, M, R, n) + \lambda\mathbb{1}$ are $(\sigma(U(w)) - \sigma(V(w)))^2 - 1$: equal to $-1$ when $w$ solves the instance and nonnegative otherwise, for every rational $\lambda$. The instance is rational when $\lambda$ is. Hence some $n \geq 1$ makes the operator fail to be positive exactly when the instance has a solution.

## Sources

- M. Kliesch, D. Gross and J. Eisert, "Matrix-product operators and states: NP-hardness and undecidability", *Physical Review Letters* 113(16), 160503, 2014, doi:[10.1103/PhysRevLett.113.160503](https://doi.org/10.1103/PhysRevLett.113.160503). Numbering of the version read, arXiv:1404.4466v2: Problems 2 and 3 (the bounded and unbounded MPO threshold problems), Theorem 5 (undecidability), Theorem 4 (NP-hardness of the bounded problem), Lemmas 11 and 12 and their proofs in the appendix, including Equation (C5).
