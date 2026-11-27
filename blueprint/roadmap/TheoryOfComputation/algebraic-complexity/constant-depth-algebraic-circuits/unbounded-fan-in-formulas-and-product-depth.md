# Unbounded fan-in arithmetic formulas and circuits of bounded product-depth

An *unbounded fan-in arithmetic circuit* over a field $K$ is a DAG whose leaves are variables or constants and whose inner gates are sum gates (computing $K$-linear combinations of their children) and product gates (computing products of their children, each child read once), of unbounded fan-in; it is a *formula* if every gate has fan-out one. Its *product-depth* is the largest number of product gates on a leaf-to-root path, and its size is the number of gates (or nodes, for formulas). Consecutive sum gates can be merged, so without loss of generality layers alternate.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.
