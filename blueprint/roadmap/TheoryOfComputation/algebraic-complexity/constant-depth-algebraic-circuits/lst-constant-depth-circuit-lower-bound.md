# Constant-depth algebraic circuits for IMM need superpolynomial size

Over every field, for every constant product-depth $\Delta$ and every $c$, for all large $n$, every unbounded fan-in arithmetic circuit of product-depth $\Delta$ computing $\mathrm{IMM}_{n,d}$ with $d=\lfloor\log_2\lfloor\log_2n\rfloor\rfloor$ has more than $n^c$ gates. Explicitly, with $N$ the number of variables, $2^{k(d^{1/(4^\Delta-1)}/20-1/2)}\le \mathrm{poly}\bigl((\mathrm{size}+N+1)^{2\Delta+1},\Theta(d/\ln d)^d\bigr)$ whenever $10d\le k$, $2^k\le n$ and $\Delta\ge1$, with the polynomial of the formula lower bound.

## Proof sketch

A circuit of product-depth $\Delta$ and size $s$ unfolds into a formula of product-depth $\Delta$ and size at most $(s+N+1)^{2\Delta+1}$; apply the formula lower bound. For constant $\Delta$ the right side is polynomial in the size times $(d/\ln d)^{O(d)}=n^{o(1)}$, while the left side is $n^{\Omega(d^{1/(4^\Delta-1)})}$ with $k=\lfloor\log_2 n\rfloor$.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field](lst-constant-depth-formula-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.
