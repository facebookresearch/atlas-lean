# Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field

Over every field, let $10d\le k$, $2^k\le n$ and $\Delta\ge1$. Every unbounded fan-in formula of product-depth at most $\Delta$ computing $\mathrm{IMM}_{n,d}$ (with its variables renamed) with $s$ nodes satisfies

$$
2^{k\left(d^{1/(4^\Delta-1)}/20-1/2\right)}\le \mathrm{poly}\bigl(s,\Theta(d/\ln d)^d\bigr),
$$

with the polynomial and the implied constants of the set-multilinearization bound. For constant $\Delta$, taking $k=\lfloor\log_2n\rfloor$ and $d=\lfloor\log_2 k\rfloor$ makes the left side $n^{\Omega(d^{1/(4^\Delta-1)})}$ while $(d/\ln d)^d=n^{o(1)}$, so constant-depth formulas for $\mathrm{IMM}_{n,d}$ need superpolynomial size.

## Proof sketch

Set-multilinearize the formula (Forbes's characteristic-free version): this gives a set-multilinear formula of product-depth at most $2\Delta$ and size $\mathrm{poly}(s,\Theta(d/\ln d)^d)$. Apply the set-multilinear lower bound at product-depth $2\Delta$, where the exponent $d^{1/(2^{2\Delta}-1)}=d^{1/(4^\Delta-1)}$.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Set-multilinearization of constant-depth formulas over any field](set-multilinearization-over-any-field.md)
- [LST lower bound for set-multilinear formulas computing IMM](lst-set-multilinear-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024, Corollary 27.
