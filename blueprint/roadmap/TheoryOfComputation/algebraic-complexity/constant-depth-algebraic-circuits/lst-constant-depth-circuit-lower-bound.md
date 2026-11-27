# Constant-depth algebraic circuits for IMM need superpolynomial size

Over every field, if $d = o(\log n)$, then every unbounded fan-in arithmetic circuit of product-depth at most $\Delta$ computing the iterated matrix multiplication polynomial $\mathrm{IMM}_{n,d}$ needs

$$
n^{\Theta\left(d^{1/(F_{2\Delta+2}-1)}/\Delta\right)}
$$

nodes (size), where $F_k$ is the $k$-th Fibonacci number ($F_0 = 0$, $F_1 = F_2 = 1$). Hence for every constant product-depth $\Delta$, if $d = d(n)$ tends to infinity with $d = o(\log n)$, such circuits have superpolynomial size.

## Proof sketch

Restrict to a word polynomial of $\mathrm{IMM}$ by setting variables to constants. Set-multilinearize over any field: Forbes shows by gate simulation that a circuit of size $s$ and product-depth $\Delta$ yields a set-multilinear circuit of product-depth $2\Delta$ and size $\mathrm{poly}(s,\Theta(d/\ln d)^d)$, and that the Limaye–Srinivasan–Tavenas argument, which over fields of characteristic $0$ or greater than $d$ first homogenizes, goes through over every field. The set-multilinear lower bound for $\mathrm{IMM}$ then gives the stated size, with the improved parameters of Bhargav, Dutta and Saxena. (Derived, not stated in this form by the sources: tracking the constants gives an absolute constant $c \ge 1$ such that for $d,k,\Delta\ge1$ with $k\ge10d$ and $2^k\le n$ every such circuit with $s\ge2$ nodes satisfies $\bigl(s\cdot d^{d}\cdot 2^{k}\bigr)^{c\Delta} \ge 2^{k(d^{1/(4^\Delta-1)}/20-1/2)}$.)

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Set-multilinearization of constant-depth formulas over any field](set-multilinearization-over-any-field.md)
- [LST lower bound for set-multilinear formulas computing IMM](lst-set-multilinear-lower-bound.md)

## Sources

- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), LIPIcs 300, 2024, Theorem 10 (stated in Section 2.1 as the Main Theorem) and Corollary 27.
- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021, Corollary 4 (over fields of characteristic $0$ or greater than $d$).
