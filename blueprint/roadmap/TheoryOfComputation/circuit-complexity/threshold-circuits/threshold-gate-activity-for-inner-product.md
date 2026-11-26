# Threshold-gate activity lower bounds for inner product

For a weighted threshold circuit, the *input-reading transcript* of an input is the vector of values of the gates that read original inputs. For any split of the coordinates into $L\cup R$ and sets $A\subseteq\{0,1\}^L$, $B\subseteq\{0,1\}^R$: if every monochromatic sub-rectangle $A'\times B'$ of the circuit's function has area at most $M$, then $|A||B|\le M\,\mathcal{A}^2$, where $\mathcal{A}$ is the number of attainable transcripts. For inner product modulo two on $m$ pairs of bits this gives $2^m\le\mathcal{A}^2$; bounding $\mathcal{A}$ by a Hamming ball of radius $\kappa$ around a baseline transcript (where $\kappa$ bounds the number of the $q$ input-reading gates whose value differs from the baseline) yields the size–activity trade-off $m/2\le\kappa\log_2(\mathrm{e}\,q/\kappa)$.

## Proof sketch

Each transcript determines a combinatorial rectangle of inputs on which the circuit output is constant (weighted threshold gates reading inputs split additively across $L$ and $R$); inner product has no monochromatic rectangles of area above $2^m$, by Lindsey's lemma.

## Depends on

- [Threshold gates and the basis of threshold circuits](../parallel-circuit-hierarchies/threshold-gates-and-threshold-circuits.md)
- [Rectangle lemma](../../communication-complexity/deterministic-communication-protocols/transcript-eq-iff.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Russell Impagliazzo, Ramamohan Paturi, Michael E. Saks, "Size–Depth Tradeoffs for Threshold Circuits", SIAM Journal on Computing, 1997.
