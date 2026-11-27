# Lifting with low-discrepancy gadgets

For every $\eta > 0$ there is $c = O\big(\eta^{-2} \log(1/\eta)\big)$ such that the following holds. Let $R$ be a search problem on $n$ bits and let $g : \{0,1\}^b \times \{0,1\}^b \to \{0,1\}$ be any gadget with uniform discrepancy $\mathrm{disc}_{\mathrm{unif}}(g) \le 2^{-\eta b}$ and $b \ge c \log n$. Then

$$D^{cc}(R \circ g^n) = \Omega\big(D^{dt}(R) \cdot b\big),$$

with a constant in $\Omega$ that depends only on $\eta$ (it cannot be absolute: the inner product of the first $\lceil 2\eta b\rceil$ bits of each $b$-bit block has uniform discrepancy at most $2^{-\eta b}$ but communication complexity $O(D^{dt}(R)\,\eta b)$ for large $b$); with the trivial simulation, $D^{cc}(R \circ g^n) = \Theta(D^{dt}(R) \cdot b)$ when $D^{cc}(g) = O(b)$. This applies to the inner product gadget on $b$-bit strings, whose uniform discrepancy is at most $2^{-b/2}$ (so $\eta = 1/2$); for $b = 1$ it is exactly $1/2$, since the largest absolute rectangle sum of the sign matrix with rows $(1,1)$ and $(1,-1)$ is $2$. The same paper proves the analogous randomized lifting theorem.

## Proof sketch

Follow the simulation of the index-gadget proof with blockwise min-entropy of both players' sets as the density measure: low uniform discrepancy makes the gadget an extractor for independent high-min-entropy sources, and its XOR powers have exponentially small discrepancy, so parities of gadget outputs on a dense rectangle are nearly unbiased, which keeps every value of the unqueried bits possible; each density-restoring step costs few queries per bit of communication.

## Depends on

- [Index gadget and lifted search problems](index-gadget-and-lifted-search-problems.md)
- [Discrepancy of a function under a distribution](../discrepancy-corruption-and-sign-rank/discrepancy-under-a-distribution.md)

## Proof depends on

- [XOR products have exponentially small discrepancy](../discrepancy-corruption-and-sign-rank/xor-products-and-discrepancy.md)
- [Low-discrepancy gadgets extract from independent min-entropy sources](../discrepancy-corruption-and-sign-rank/low-discrepancy-gadgets-are-extractors.md)
- [Density-restoring partition](density-restoring-partition.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021 (Definition 1.1 and Theorem 1.2).
