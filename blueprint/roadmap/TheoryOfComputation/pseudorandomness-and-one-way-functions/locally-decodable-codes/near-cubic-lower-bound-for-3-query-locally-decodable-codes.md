# Near-cubic lower bound for 3-query locally decodable codes

Every 3-query locally decodable code from $k$ message bits to $n$ codeword bits with constant decoding parameters has $n\ge k^3/\mathrm{polylog}(k)$, improving the previous near-quadratic bound by a polynomial factor via refutation of semirandom 3-XOR instances.

A code $\mathcal{C}:\{0,1\}^k\to\{0,1\}^n$ is $(q,\delta,\varepsilon)$-locally decodable if a randomized algorithm $\mathrm{Dec}$ with oracle access to $y\in\{0,1\}^n$ and input $i\in[k]$ makes at most $q$ queries and satisfies $\Pr[\mathrm{Dec}^y(i)=b_i]\ge\frac12+\varepsilon$ for all $b\in\{0,1\}^k$, $i\in[k]$ and $y$ with relative Hamming distance $\Delta(y,\mathcal{C}(b))\le\delta$. If $\mathcal{C}$ is $(3,\delta,\varepsilon)$-locally decodable, then

$$
k^3\le n\cdot O\left(\frac{\log^{14}n}{\varepsilon^{32}\delta^{16}}\right).
$$

In particular, $n\ge k^3/\mathrm{polylog}(k)$ when $\delta,\varepsilon$ are constants. Known relations between locally correctable and locally decodable codes give a similar lower bound for 3-query locally correctable codes. For comparison, 2-query codes need $n=\exp(\Omega(k))$, while the best 3-query constructions have $n=\exp(k^{o(1)})$.

## Expansion

Pass to normal form: for each $i$ there is a 3-uniform hypergraph matching $\mathcal{H}_i$ with at least $\delta n$ hyperedges $C$ such that $\Pr_b[b_i=\prod_{v\in C}\mathcal{C}(b)_v]\ge\frac12+\varepsilon$. For a random message $b$, the codeword satisfies a $\frac12+\varepsilon$ fraction of the 3-XOR constraints $\prod_{v\in C}x_v=b_i$, $C\in\mathcal{H}_i$, whose right-hand sides are random. Decompose the hypergraphs at a degree threshold $d$: hyperedges through pairs of vertices of high co-degree become a bipartite 2-XOR instance, and the rest form a 3-XOR instance with all pair degrees at most $d=O(\log n/\varepsilon^2\delta^2)$. Bounding the $(\infty\to 1)$-norm of a Kikuchi matrix built from the 3-XOR part, after a Cauchy–Schwarz step and row pruning, bounds the expected 3-XOR value, and a matrix Bernstein bound makes the expected 2-XOR value at most $\varepsilon\delta nk/3$. Since the $m\ge\delta nk$ constraints have expected value at least $2\varepsilon m\ge 2\varepsilon\delta nk$, comparing the two sides forces $k^3\le n\cdot O(\log^{14}n/\varepsilon^{32}\delta^{16})$.

## Depends on

- [Locally decodable codes and smooth decoders](locally-decodable-codes-and-smooth-decoders.md)

## Proof depends on

- [Smooth decoders yield large decoding matchings](smooth-decoders-yield-decoding-matchings.md)
- [Matrix Bernstein inequality, Hermitian case](../../../Probability/concentration-inequalities/matrix-concentration-inequalities/matrix-bernstein.md)

## Sources

- Omar Alrabiah, Venkatesan Guruswami, Pravesh K. Kothari and Peter Manohar, "A Near-Cubic Lower Bound for 3-Query Locally Decodable Codes from Semirandom CSP Refutation", *Proceedings of the 55th ACM Symposium on Theory of Computing (STOC 2023)*, 2023, https://doi.org/10.1145/3564246.3585143 (Theorem 1, Definitions 2.2 and 2.3, Fact 2.4, Lemmas 3.2, 3.3 and 3.4, Lemma 4.1, Definition 4.3; constants and numbering of the original 2022 version of ECCC Report TR22-101 read, which later revisions of that report change).
