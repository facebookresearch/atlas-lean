# Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field

Over every field, with the absolute constant $c$ of the circuit bound, let $d,k,\Delta\ge1$ with $k\ge10d$ and $2^k\le n$. Every unbounded fan-in formula of product-depth at most $\Delta$ with $s\ge2$ nodes computing $\mathrm{IMM}_{n,d}$ satisfies

$$
\bigl(s\cdot d^{d}\cdot 2^{k}\bigr)^{c\Delta}\ \ge\ 2^{k\left(d^{1/(4^\Delta-1)}/20-1/2\right)} .
$$

For constant $\Delta$, taking $k=\lfloor\log_2n\rfloor$ and $d=\lfloor\log_2 k\rfloor$ makes the right side $n^{\Omega(d^{1/(4^\Delta-1)})}$ while $d^d=n^{o(1)}$, so constant-depth formulas for $\mathrm{IMM}_{n,d}$ need superpolynomial size.

## Proof sketch

A formula is a circuit of the same size and product-depth, so the circuit bound applies.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Constant-depth algebraic circuits for IMM need superpolynomial size](lst-constant-depth-circuit-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), LIPIcs 300, 2024, Theorem 10 and Corollary 27.
