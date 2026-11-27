# Barak-Rao-Shaltiel-Wigderson: two-source dispersers for subpolynomial entropy

There are explicit two-source dispersers for min-entropy $n^{o(1)}$; consequently there are explicit $K$-Ramsey graphs on $N$ vertices with $K = 2^{2^{(\log\log N)^{1 - \alpha_0}}}$ for an absolute constant $\alpha_0 > 0$, beating the Frankl-Wilson construction.

## Proof sketch

The construction is a challenge-response mechanism: one source is used to select a somewhere-random block structure in the other, and a sequence of "challenges" computed by extractors from the blocks are answered using the first source, identifying a block of high entropy with certainty. Recursion on the block structure reduces the entropy requirement to $n^{o(1)}$.

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Sources

- Boaz Barak, Anup Rao, Ronen Shaltiel, Avi Wigderson, "2-source dispersers for n^{o(1)} entropy, and Ramsey graphs beating the Frankl-Wilson construction", Annals of Mathematics 176(3) (2012).
