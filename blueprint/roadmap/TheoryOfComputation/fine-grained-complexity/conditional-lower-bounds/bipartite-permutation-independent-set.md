# ETH lower bound for bipartite permutation independent set

In the $2n\times 2n$ Bipartite Permutation Independent Set problem, the input is a graph on $[2n]\times[2n]$ and the question is whether there is an independent set containing exactly one vertex in each row and column of each of the four $n\times n$ quadrants, forming a permutation pattern. Assuming ETH, this problem cannot be solved in time $2^{o(n\log n)}$.

## Proof sketch

Reduce 3-Coloring on $N$ vertices, which needs $2^{\Omega(N)}$ under ETH, by grouping vertices into blocks of size $\Theta(\log n)$ and encoding the colorings of a block as rows of a permutation grid, so that $N=\Theta(n\log n)$.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Proof depends on

- [Impagliazzo–Paturi–Zane sparsification and ETH in terms of clauses](../sat-exponents-and-hypotheses/sparsification-lemma.md)

## Sources

- Daniel Lokshtanov, Dániel Marx and Saket Saurabh, "Slightly Superexponential Parameterized Problems", SIAM Journal on Computing 47(3), 2018, Theorem 2.11.
- Rahul Ilango, "Approaching MCSP from Above and Below: Hardness for a Conditional Variant and AC^0[p]", 11th Innovations in Theoretical Computer Science Conference (ITCS 2020), 2020.
