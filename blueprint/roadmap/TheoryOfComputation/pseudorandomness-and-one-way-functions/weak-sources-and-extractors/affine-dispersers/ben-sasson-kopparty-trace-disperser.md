# Ben-Sasson–Kopparty: the trace of an elementary symmetric polynomial is an affine disperser

Let $t<r$ be positive integers, let $n$ be a prime with $n\ge r(r+1)/t$, let $F=\mathbb{F}_{2^n}$ and $\mu\in F^\times$. For $i\in[r]$ put $e_i=r+1-i$ and $\alpha_i=\sum_{k=0}^{e_i}2^k=2^{r+2-i}-1$, and define $f:F^r\to\mathbb{F}_2$ by

$$
f(x_1,\dots,x_r)=\mathrm{Tr}_{F/\mathbb{F}_2}\Bigl(\mu\sum_{I\subseteq[r],\ |I|=t}\ \prod_{i\in I}x_i^{\alpha_i}\Bigr).
$$

Then $f$ is nonconstant on every $\mathbb{F}_2$-affine subspace $A\subseteq F^r$ with

$$
\dim A>\frac{nr}{t}+nt+r(r+1).
$$

Composing with an injective $\mathbb{F}_2$-linear map $\{0,1\}^N\to F^r$ (so $N\le rn$) gives a function on $\{0,1\}^N$ that is nonconstant on every affine subspace of dimension greater than $nr/t+nt+r(r+1)$.

## Proof sketch

Restricted to $A$, write each coordinate through a subspace polynomial and decompose $A$ into a triangular family of pivot subspaces (Bourgain's decomposition). The restricted function is a reduced polynomial; the structural lemma on coefficients of subspace polynomials, together with a choice of exponents for which one monomial has a single nonvanishing contribution, isolates a nonzero coefficient, and a nonzero reduced polynomial is a nonconstant function. Primality of $n$ rules out proper subfields other than $\mathbb{F}_2$.

## Depends on

- [Affine dispersers](../../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)
- [The Galois field with pⁿ elements](../../../../FieldTheory/finite-fields/finite-field-existence.md)

## Sources

- E. Ben-Sasson and S. Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing 41(4), 880–914, 2012, Theorem 7.3 (case $p=2$), Lemmas 3.10, 3.13 and 7.1.
