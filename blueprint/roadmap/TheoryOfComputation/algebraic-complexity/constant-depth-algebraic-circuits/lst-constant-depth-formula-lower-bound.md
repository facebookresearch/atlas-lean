# Limaye–Srinivasan–Tavenas lower bound for constant-depth formulas over any field

Over every field, if $d = o(\log n)$, then unbounded fan-in formulas of product-depth at most $\Delta$ computing $\mathrm{IMM}_{n,d}$ need

$$
n^{\Theta\left(d^{1/(F_{2\Delta+2}-1)}/\Delta\right)}
$$

nodes, where $F_k$ is the $k$-th Fibonacci number; in particular, for constant $\Delta$ and $d = d(n)$ tending to infinity with $d = o(\log n)$, constant-depth formulas for $\mathrm{IMM}_{n,d}$ need superpolynomial size.

## Proof sketch

A formula is a circuit of the same size and product-depth, so the circuit bound applies. (Derived, not stated in this form by the sources: the explicit inequality $\bigl(s\cdot d^{d}\cdot 2^{k}\bigr)^{c\Delta} \ge 2^{k(d^{1/(4^\Delta-1)}/20-1/2)}$ for $k\ge10d$, $2^k\le n$ and $s \ge 2$ nodes, with the absolute constant $c$ of the derived circuit bound, holds for formulas as well; taking $k=\lfloor\log_2n\rfloor$ and $d=\lfloor\log_2 k\rfloor$ makes the right side $n^{\Omega(d^{1/(4^\Delta-1)})}$ while $d^d=n^{o(1)}$.)

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Constant-depth algebraic circuits for IMM need superpolynomial size](lst-constant-depth-circuit-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), LIPIcs 300, 2024, Theorem 10 (stated for circuits, which include formulas) and Corollary 27.
