# Set-multilinearization of constant-depth formulas over any field

Over any field, let the variables be partitioned into blocks $X_1,\dots,X_d$, and let $f$ be computed by an unbounded fan-in circuit (in particular, a formula) of product-depth $\Delta$ and size $s$. Then the set-multilinear part of $f$ on all $d$ blocks (the sum of the monomials of $f$ that contain exactly one variable from each block) is computed by a syntactically set-multilinear circuit of product-depth at most $2\Delta$ and size at most $\mathrm{poly}\bigl(s,\Theta(d/\ln d)^d\bigr)$; the polynomial and the implied constants are absolute. When $f$ itself is set-multilinear, this circuit computes $f$.

## Proof sketch

Gate simulation: every gate $v$ is replaced by its set-multilinear parts $v_S$ on all sets $S$ of blocks. A linear combination of gates is simulated part by part, adding no product-depth. For a product gate $v=v_1\cdots v_m$, normalize the factors with nonzero constant term to have constant term $1$; the part $v_S$ is then a sum, over the set partitions of $S$, of $k$-surjective rectangular permanents of matrices whose entries are parts of the factors, and the Binet–Minc identity computes each such permanent by a set-multilinear product-depth-two formula of size $\mathrm{poly}(m,\Theta(\ell/\ln\ell)^{\ell})$ for $|S|=\ell$. Each product layer thus becomes at most two product layers, and no step depends on the characteristic.

## Depends on

- [Set-multilinear polynomials and formulas](set-multilinear-polynomials-and-formulas.md)

## Proof depends on

- [Rectangular permanents and the Binet–Minc identity](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/rectangular-permanents-binet-minc-identity.md)

## Sources

- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), LIPIcs 300, 2024, Lemmas 25 and 26 and Corollary 27.
- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021 (the characteristic-dependent version, via homogenization).
