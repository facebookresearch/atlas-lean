# A traceless Hermitian matrix is a commutator of small Hermitian matrices

Let $d \ge 2$ and let $H$ be a traceless Hermitian $d \times d$ matrix. Then there are traceless Hermitian $d \times d$ matrices
$F$ and $G$ with

$$[F, G] = i H \qquad\text{and}\qquad \| F \|, \| G \| \le d^{1/4} \Big( \frac{d - 1}{2} \Big)^{1/2} \sqrt{\| H \|} .$$

Proof: if $H = 0$ take $F = G = 0$. Otherwise, in a basis Fourier-conjugate to an eigenbasis of $H$ the diagonal entries of $H$ are $\operatorname{tr}(H)/d = 0$.
Take $G = \operatorname{diag}(-(d-1)/2, -(d-1)/2 + 1, \dots, (d-1)/2)$ and $F_{jk} = i H_{jk} / (G_{kk} - G_{jj})$ for
$j \ne k$, $F_{jj} = 0$. Then $F$ and $G$ are Hermitian and traceless (zero and centred diagonals) with $[F, G] = iH$, $|F_{jk}| \le |H_{jk}|$, so
$\| F \|^2 \le \operatorname{tr}(F^2) \le \operatorname{tr}(H^2) \le d \| H \|^2$, and $\| G \| = (d - 1)/2$; since $F \ne 0$,
rescaling $F \mapsto \lambda F$, $G \mapsto G / \lambda$ with $\lambda = \sqrt{\| G \| / \| F \|}$ makes both norms equal to
$\sqrt{\| F \| \| G \|}$ and keeps both traces zero.

## Proof depends on

- [Spectral theorem for normal matrices](../../../LinearAlgebra/eigenvalues-and-canonical-forms/spectral-theorem-for-normal-matrices/exists-unitary-diagonal-of-is-star-norma.md): an eigenbasis of $H$

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 5.2, Lemma 2 and its proof, equations (24)–(31).
