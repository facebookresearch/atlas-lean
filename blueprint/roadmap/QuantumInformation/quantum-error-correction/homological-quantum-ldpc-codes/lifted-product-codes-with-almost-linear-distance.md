# Panteleev-Kalachev: lifted product codes with almost linear distance

There are quasi-cyclic lifted product quantum LDPC codes with distance $d = \Omega(n / \log n)$ and dimension $k = \Theta(\log n)$; more generally, for every $0 \le \alpha < 1$ there are quantum LDPC codes, homological products of these codes with a classical LDPC code (not lifted product codes $\mathrm{LP}(A, B)$ themselves), with $k = \Omega(n^{\alpha}\log n)$ and $d = \Omega(n^{1 - \alpha/2}/\log n)$.

## Proof sketch

Take $A$ to be a random lift (over a cyclic group of order $\ell$) of a constant-size base matrix, whose underlying Tanner graph is a good expander and whose code is good, and $B = 1 + x$ type matrices or another lifted matrix. Expansion of the lifted Tanner graph shows that every nontrivial logical operator, viewed through the quotient by the cyclic group, has weight linear in $n$ up to the $\log$ coming from the cyclic factor. For the second family, take such a code $Q$ with parameters $[[N, K, D]]$ and a good classical LDPC $[m, \Theta(m), \Theta(m)]$ code $C$ with $m = \Theta(N^{\alpha/(2(1-\alpha))})$, and form the homological product $(Q \otimes C)^{*} \otimes C$: its length is $O(m^2 N)$, its dimension $\Theta(m^2 K)$ and its distance $\Omega(m D)$.

## Depends on

- [Lifted product codes over group algebras](lifted-product-codes-over-group-algebras.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Quantum LDPC codes with almost linear minimum distance", IEEE Transactions on Information Theory 68(1) (2022); arXiv:2012.04068 (Theorems 1 and 2, equation (2)).
