# Panteleev-Kalachev: lifted product codes with almost linear distance

There are quasi-cyclic lifted product quantum LDPC codes with distance $d = \Omega(n / \log n)$ and dimension $k = \Theta(\log n)$; more generally, for every $0 \le \alpha < 1$ there are lifted product LDPC codes with $k = \Theta(n^{\alpha}\log n)$ and $d = \Omega(n^{1 - \alpha/2}/\log n)$.

## Proof sketch

Take $A$ to be a random lift (over a cyclic group of order $\ell$) of a constant-size base matrix, whose underlying Tanner graph is a good expander and whose code is good, and $B = 1 + x$ type matrices or another lifted matrix. Expansion of the lifted Tanner graph shows that every nontrivial logical operator, viewed through the quotient by the cyclic group, has weight linear in $n$ up to the $\log$ coming from the cyclic factor.

## Depends on

- [Lifted product codes over group algebras](lifted-product-codes-over-group-algebras.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Quantum LDPC codes with almost linear minimum distance", IEEE Transactions on Information Theory 68(1) (2022); arXiv:2012.04068.
