# Cosystolic expansion of a cochain complex

Let $X$ be a finite simplicial (or cell) complex with $\mathbb{F}_2$-cochain spaces $C^i$, coboundary maps $\delta_i : C^i \to C^{i+1}$, cocycles $Z^i = \ker\delta_i$ and normalized weights $\|f\|$ (e.g. the fraction of $i$-cells in the support of $f$, possibly weighted). $X$ is an *$(\varepsilon, \mu)$-cosystolic expander in dimension $i$* if

1. for every $f \in C^i \setminus Z^i$: $\|\delta_i f\| \ge \varepsilon \cdot \min_{z \in Z^i} \|f - z\|$, and
2. every cocycle $z \in Z^i \setminus \mathrm{im}\,\delta_{i-1}$ satisfies $\|z\| \ge \mu$ (large cosystoles).

## Depends on

- [Binary chain complexes of length two and their homology](binary-chain-complexes-of-length-two.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)

## Sources

- Shai Evra, Tali Kaufman, Gilles Zemor, "Decodable quantum LDPC codes beyond the sqrt(n) distance barrier using high dimensional expanders", FOCS (2020), SIAM Journal on Computing (2024); arXiv:2004.07935.
