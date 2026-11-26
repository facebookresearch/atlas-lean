# Affine dispersers exist when n(d+1)+1 < 2^d

For all $n, d$ with $n(d+1) + 1 < 2^d$ there is an affine disperser $f : \{0,1\}^n \to \{0,1\}$ for dimension $d$ (for example $n = 100$, $d = 11$).

## Proof sketch

There are at most $2^{n(d+1)}$ affine maps $\{0,1\}^d \to \{0,1\}^n$, and at most $2 \cdot 2^{2^n - 2^d}$ functions are constant on the image of a given injective one. Their product is less than the $2^{2^n}$ functions on $n$ bits.

## Depends on

- [Affine dispersers](../../circuit-complexity/lower-bounds-for-general-circuits-and-formulas/gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)

## Sources

- O. S. Mishra and R. Santhanam, "An Explicit 3.5n − o(n) Size Lower Bound against General Boolean Circuits", Electronic Colloquium on Computational Complexity, report TR26-260, 2026.
