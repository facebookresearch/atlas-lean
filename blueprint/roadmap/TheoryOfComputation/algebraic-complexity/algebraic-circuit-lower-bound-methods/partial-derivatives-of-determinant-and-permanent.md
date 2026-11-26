# Partial derivatives of the generic determinant and permanent

For $0\le k\le n$, the $k$-th order partial derivatives of the generic $n\times n$ determinant (respectively permanent) include, up to sign, all its $(n-k)\times(n-k)$ minors (respectively sub-permanents). These have pairwise disjoint sets of monomials, so they are linearly independent over every field, and $\mu_k(\det_n),\mu_k(\mathrm{per}_n)\ge\binom nk^2$.

## Proof sketch

Differentiating with respect to $x_{i_1j_1},\dots,x_{i_kj_k}$ with distinct rows and columns deletes those rows and columns; distinct row and column sets give disjoint monomial supports.

## Depends on

- [The partial-derivative measure](partial-derivative-measure.md)
- [Leibniz formula for the determinant](../../../LinearAlgebra/determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/det-apply.md)
- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Sources

- Neeraj Kayal, Ramprasad Saptharishi, "A Selection of Lower Bounds for Arithmetic Circuits", Perspectives in Computational Complexity: The Somenath Biswas Anniversary Volume, 2014.
- Noam Nisan, Avi Wigderson, "Lower Bounds on Arithmetic Circuits via Partial Derivatives", Computational Complexity, 1996.
