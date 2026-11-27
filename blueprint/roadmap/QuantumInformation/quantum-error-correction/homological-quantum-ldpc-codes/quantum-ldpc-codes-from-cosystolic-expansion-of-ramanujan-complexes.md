# Evra-Kaufman-Zemor: decodable quantum LDPC codes with distance above the square root

Ramanujan complexes, which are cosystolic expanders, yield explicit families of quantum LDPC codes of length $n$ with (i) dimension $k = \Omega(\sqrt{n/\log n})$ and distance $d = \Omega(\sqrt{n\log n})$, from $2$-dimensional complexes, together with a polynomial-time decoder correcting every adversarial error pattern of weight up to a constant fraction of $d$; and (ii) dimension $k = \Omega(\sqrt{n}/\log n)$ and distance $d = \Omega(\sqrt{n}\log n)$, from $3$-dimensional complexes.

## Proof sketch

The quantum code of a $2$-dimensional Ramanujan complex has $Z$-distance $\Omega(n)$ (a cosystole bound from cosystolic expansion) and $X$-distance $\Omega(\log n)$ (a systole bound); for $3$-dimensional complexes the $2$-systole is $\Omega(\log^{2} n)$. A distance-balancing product with an asymptotically good classical LDPC code, generalizing constructions of Hastings and of Tillich-Zemor, equalizes the two distances. For family (i), $X$-errors of the component code are decoded by minimum-weight matching and $Z$-errors by a local flip decoder whose correctness follows from coboundary expansion of the complex.

## Depends on

- [Cosystolic expansion and cosystolic distance](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/cosystolic-expansion.md)
- [The CSS code of a chain complex](css-code-of-a-chain-complex.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Sources

- Shai Evra, Tali Kaufman, Gilles Zemor, "Decodable quantum LDPC codes beyond the sqrt(n) distance barrier using high dimensional expanders", FOCS (2020), SIAM Journal on Computing (2024); arXiv:2004.07935.
