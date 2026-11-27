# Constant-depth algebraic circuits for IMM need superpolynomial size

Over every field there is an absolute constant $c\ge1$ such that the following holds. Let $d,k,\Delta\ge1$ with $k\ge10d$ and $2^k\le n$. Every unbounded fan-in arithmetic circuit of product-depth at most $\Delta$ with $s\ge2$ nodes computing $\mathrm{IMM}_{n,d}$ satisfies

$$
\bigl(s\cdot d^{d}\cdot 2^{k}\bigr)^{c\Delta}\ \ge\ 2^{k\left(d^{1/(4^\Delta-1)}/20-1/2\right)} .
$$

Hence for every constant product-depth $\Delta$ and every $c'$, for all large $n$, every such circuit computing $\mathrm{IMM}_{n,d}$ with $d=\lfloor\log_2\lfloor\log_2n\rfloor\rfloor$ has more than $n^{c'}$ nodes.

## Proof sketch

Restrict to $\mathrm{IMM}_{2^k,d}$ by setting variables to $0$. Set-multilinearize over any field: this gives a set-multilinear circuit of product-depth at most $2\Delta$ and size $\mathrm{poly}(s,\Theta(d/\ln d)^d)\le(s\,d^d)^{O(1)}$. Substitute linear forms to pass to the word polynomial $P_w$ of the greedy $k$-unbiased word (size grows by a factor at most $2^k+2$), unfold the result into a set-multilinear formula (the exponent grows by a factor $O(\Delta)$), and apply the set-multilinear lower bound at product-depth $2\Delta$, where $d^{1/(2^{2\Delta}-1)}=d^{1/(4^\Delta-1)}$. For constant $\Delta$ and $k=\lfloor\log_2n\rfloor$, the right side is $n^{\Omega(d^{1/(4^\Delta-1)})}$ while $d^d=n^{o(1)}$.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Set-multilinearization of constant-depth formulas over any field](set-multilinearization-over-any-field.md)
- [LST lower bound for set-multilinear formulas computing IMM](lst-set-multilinear-lower-bound.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021, Corollary 4 (over fields of characteristic $0$ or greater than $d$).
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), LIPIcs 300, 2024, Theorem 10 and Corollary 27 (over every field).
