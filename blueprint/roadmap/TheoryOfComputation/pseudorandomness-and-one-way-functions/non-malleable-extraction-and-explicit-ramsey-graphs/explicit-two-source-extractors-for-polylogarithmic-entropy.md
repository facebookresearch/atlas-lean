# Chattopadhyay-Zuckerman: explicit two-source extractors for polylogarithmic min-entropy

There is a constant $C$ such that for all $n$ there is an explicit function $\mathrm{Ext} : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ which is a two-source extractor for independent sources of min-entropy $\log^{C} n$ with error $n^{-\Omega(1)}$; moreover, the extractor is strong in the second source. Consequently there are explicit $K$-Ramsey graphs on $N$ vertices with $K = 2^{(\log\log N)^{O(1)}}$.

## Proof sketch

Apply a seeded extractor with seed length $O(\log n)$ to the second source under each of its $D = \mathrm{poly}(n)$ seeds, and use the $D$ outputs as seeds of a $t$-non-malleable extractor (seed length $O(t^2\log^2(n/\varepsilon))$) applied to the first source. This produces a table of $D$ bits in which, for most fixings of the second source, all but a few bits are $t$-wise nearly independent and uniform. Applying a resilient function (a derandomized Ajtai-Linial function) tolerant to the few bad coordinates yields a nearly unbiased bit.

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Seeded non-malleable extractors (Dodis-Wichs)](seeded-non-malleable-extractors.md)
- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Sources

- Eshan Chattopadhyay, David Zuckerman, "Explicit two-source extractors and resilient functions", Annals of Mathematics 189(3) (2019), STOC (2016); ECCC TR15-119.
