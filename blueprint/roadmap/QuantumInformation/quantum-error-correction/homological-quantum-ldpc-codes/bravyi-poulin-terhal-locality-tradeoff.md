# Bravyi-Poulin-Terhal tradeoff for geometrically local codes

For every family of stabilizer codes $[[n, k, d]]$ whose generators are supported on balls of constant radius in a $D$-dimensional cubic lattice ($D \ge 2$): $d = O(n^{(D-1)/D})$ (Bravyi-Terhal), and

$$
k\, d^{2/(D-1)} = O(n) .
$$

In particular two-dimensional local codes satisfy $k d^2 = O(n)$, so geometrically local codes cannot be asymptotically good, and achieving good parameters requires expander-like (non-Euclidean) connectivity.

## Proof sketch

Partition the lattice into correctable regions (sets of diameter smaller than $d$ are correctable) and a thin network of separating regions. A cleaning lemma moves any logical operator off a correctable region; covering the lattice by two correctable families plus a set of size $O(n/d^{2/(D-1)})$ that supports all logical operators bounds $k$ by the size of that set via a dimension-counting argument for complementary logical algebras.

## Depends on

- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Proof depends on

- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)

## Sources

- Sergey Bravyi, David Poulin, Barbara Terhal, "Tradeoffs for reliable quantum information storage in 2D systems", Physical Review Letters 104 (2010); arXiv:0909.5200.
- Sergey Bravyi, Barbara Terhal, "A no-go theorem for a two-dimensional self-correcting quantum memory based on stabilizer codes", New Journal of Physics 11 (2009); arXiv:0810.1983.
