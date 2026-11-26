# Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field

Over every field, let $10d\le k$, $2^k\le n$ and $\Delta\ge1$. Every unbounded fan-in formula of product-depth at most $\Delta$ computing $\mathrm{IMM}_{n,d}$ (with its variables renamed) satisfies

$$
2^{k\left(d^{1/(4^\Delta-1)}/20-1/2\right)}\le c_d^{\,\Delta}\cdot(\text{number of nodes}),\qquad c_d=4\bigl(2(d+1)^2\bigr)^{d+1}.
$$

For constant $\Delta$, taking $k=\lfloor\log_2n\rfloor$ and $d$ growing slowly with $n$ makes the left side exceed every polynomial in $n$, so constant-depth formulas for $\mathrm{IMM}_{n,d}$ need superpolynomial size.

## Proof sketch

Set-multilinearize the formula on all $d$ blocks at a cost of $c_d^\Delta$ (Forbes's characteristic-free version) and apply the set-multilinear lower bound.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Set-multilinearization of constant-depth formulas over any field](set-multilinearization-over-any-field.md)
- [LST lower bound for set-multilinear formulas computing IMM](lst-set-multilinear-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", Electronic Colloquium on Computational Complexity, 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.
