# Evra-Kaufman-Zemor: decodable quantum LDPC codes with distance above the square root

There is an explicit family of quantum LDPC codes with $k$ growing (polylogarithmically) and distance $d = \Omega(\sqrt{n}\log n)$, together with an efficient decoder correcting $\Omega(\sqrt n \log n)$ adversarial errors in one of the two error types, constructed from Ramanujan complexes that are cosystolic expanders.

## Proof sketch

Bounded-degree Ramanujan complexes of dimension at least $3$ are cosystolic expanders in dimension $1$ (Kaufman-Kazhdan-Lubotzky, Evra-Kaufman). Their $1$-cochain code has linear cosystolic distance in one direction but small distance in the other; a distance-balancing product with a classical code (in the style of Hastings) equalizes the two distances to $\Omega(\sqrt n \log n)$, and cosystolic expansion yields a greedy small-set-flip decoder.

## Depends on

- [Cosystolic expansion of a cochain complex](cosystolic-expansion-of-cochain-complexes.md)
- [The CSS code of a chain complex](css-code-of-a-chain-complex.md)

## Proof depends on

- [Cosystolic expansion of a cochain complex](cosystolic-expansion-of-cochain-complexes.md)
- [The CSS code of a chain complex](css-code-of-a-chain-complex.md)

## Sources

- Shai Evra, Tali Kaufman, Gilles Zemor, "Decodable quantum LDPC codes beyond the sqrt(n) distance barrier using high dimensional expanders", FOCS (2020), SIAM Journal on Computing (2024); arXiv:2004.07935.
