# Set-multilinearization of constant-depth formulas over any field

Over any field, let $F$ be an unbounded fan-in formula of product-depth $\Delta$ and size $s$ computing a set-multilinear polynomial $f$ of degree $d$ (in variables split into $d$ blocks). Then $f$ is computed by a syntactically set-multilinear formula of product-depth at most $2\Delta$ and size at most $\mathrm{poly}\bigl(s,\Theta(d/\ln d)^d\bigr)$.

## Proof sketch

Gate by gate, each gate $g$ is replaced by the set-multilinear parts $g_S$ of $g$ on the sets $S$ of blocks: inputs are kept on their own block and sum gates are simulated blockwise. A product gate $\prod_j f_j$ is replaced by a sum, over the ways to distribute the blocks of $S$ among the factors, of products of the corresponding parts; the factors that receive no block contribute only their constant parts, which are grouped by interpolation. Each original product layer thus becomes at most two product layers, so the product-depth at most doubles, and the blow-up per gate depends only on $d$. This argument needs no assumption on the characteristic.

## Depends on

- [Set-multilinear polynomials and formulas](set-multilinear-polynomials-and-formulas.md)

## Sources

- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024, Corollary 27.
- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
