# Cohen: two-source dispersers for polylogarithmic entropy

There are explicit two-source dispersers for min-entropy $\mathrm{polylog}(n)$, and hence explicit $K$-Ramsey graphs on $N$ vertices with $K = 2^{(\log\log N)^{O(1)}} = (\log N)^{(\log\log N)^{O(1)}}$, quasi-polynomial in $\log N$.

## Proof sketch

Cohen replaces the challenge-response mechanism by correlation breakers with advice applied to the rows of a somewhere-random matrix extracted from one source with seeds from the other, so that each row's output becomes independent of the others; a disperser outputs a non-constant function of the resulting nearly independent bits.

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Correlation breakers with advice](correlation-breakers-with-advice.md)
- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Sources

- Gil Cohen, "Two-source dispersers for polylogarithmic entropy and improved Ramsey graphs", STOC (2016), SIAM Journal on Computing 50(3) (2021); arXiv:1506.04428.
