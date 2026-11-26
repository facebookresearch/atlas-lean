# Constant-depth algebraic circuits for IMM need superpolynomial size

Over every field, for every constant product-depth $\Delta$ and every $c$, for all large $n$, every unbounded fan-in arithmetic circuit of product-depth $\Delta$ computing $\mathrm{IMM}_{n,d}$ with $d=\lfloor\log_2\lfloor\log_2n\rfloor\rfloor$ has more than $n^c$ gates. Explicitly, with $N$ the number of variables, $2^{k(d^{1/(4^\Delta-1)}/20-1/2)}\le c_d^{\,\Delta}\,(\mathrm{size}+N+1)^{2\Delta+1}$ whenever $10d\le k$, $2^k\le n$ and $\Delta\ge1$.

## Proof sketch

A circuit of product-depth $\Delta$ and size $s$ unfolds into a formula of product-depth $\Delta$ and size at most $(s+N+1)^{2\Delta+1}$; apply the formula lower bound.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field](lst-constant-depth-formula-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", Electronic Colloquium on Computational Complexity, 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.
