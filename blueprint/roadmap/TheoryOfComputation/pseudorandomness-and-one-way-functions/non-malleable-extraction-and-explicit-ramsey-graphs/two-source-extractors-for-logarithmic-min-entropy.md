# Li: two-source extractors for asymptotically optimal min-entropy and log-Ramsey graphs

There is an absolute constant $C$ such that for every $n$ there is an explicit two-source extractor $\mathrm{Ext} : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ for independent sources of min-entropy $C\log n$ with constant error. Consequently there are explicit $K$-Ramsey graphs on $N$ vertices with $K = \log^{O(1)} N$, matching Erdős's existential bound $K = O(\log N)$ up to a polynomial.

## Proof sketch

Plug the asymptotically optimal non-malleable extractor (seed length $O(\log n)$, entropy $O(\log n)$) into the efficient two-source reduction. Since the reduction's overhead is governed by the seed length and entropy of the non-malleable extractor, all quantities become $O(\log n)$, which gives the two-source extractor and, via the disperser-to-Ramsey lemma, the Ramsey graphs.

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Li: seeded non-malleable extractors with asymptotically optimal seed length](seeded-non-malleable-extractors-with-optimal-seed-length.md)
- [Ben-Aroya-Doron-Ta-Shma: an efficient reduction from two-source to non-malleable extractors](two-source-extraction-at-near-logarithmic-entropy.md)
- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Sources

- Xin Li, "Two source extractors for asymptotically optimal entropy, and (many) more", FOCS (2023); arXiv:2303.06802.
