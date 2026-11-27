# Set-multilinear polynomials and formulas

Let the variables be partitioned into blocks $X_1,\dots,X_d$. A polynomial is *set-multilinear* on a set $S$ of blocks if each of its monomials contains exactly one variable from each block in $S$ and no other variables. For any polynomial $f$ its *set-multilinear part* on $S$ is the sum of its monomials of this form. An unbounded fan-in circuit or formula is *syntactically set-multilinear* on $S$ if every gate is assigned a set of blocks, the root is assigned $S$, every leaf is a variable of a block assigned to it as a singleton (or a constant, assigned the empty set), sum gates have children with the same block set, and product gates partition their block set among their children; such a circuit computes a set-multilinear polynomial on its block set.

## Depends on

- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.
