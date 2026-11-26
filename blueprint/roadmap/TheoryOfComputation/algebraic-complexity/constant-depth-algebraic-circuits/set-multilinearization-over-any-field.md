# Set-multilinearization of constant-depth formulas over any field

Let $F$ be an unbounded fan-in formula of product-depth $\Delta$ and size $s$ over any field, in variables split into $d$ blocks. Then for every set $S$ of blocks there is a syntactically set-multilinear formula of product-depth at most $\Delta$ and size at most $c_d^{\,\Delta}\,s$ computing the set-multilinear part of $F$ on $S$, where $c_d=4(2(d+1)^2)^{d+1}$ depends only on $d$.

## Proof sketch

Gate simulation, one gate and one set of blocks at a time: inputs are kept on their own block, sum gates are simulated blockwise, and a product gate $\prod_jf_j$ is replaced by a product gadget summing over ordered partitions of $S$ among the factors, with interpolation used to group factors with empty block sets; this costs a factor depending only on $d$ per product layer and works in every characteristic.

## Depends on

- [Set-multilinear polynomials and formulas](set-multilinear-polynomials-and-formulas.md)

## Sources

- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.
- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", Electronic Colloquium on Computational Complexity, 2021.
