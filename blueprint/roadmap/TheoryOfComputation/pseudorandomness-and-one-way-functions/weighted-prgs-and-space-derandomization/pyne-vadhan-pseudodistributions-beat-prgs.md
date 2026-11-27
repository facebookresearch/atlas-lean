# Pyne–Vadhan: weighted PRGs for unbounded-width permutation ROBPs with seed Õ(log^{3/2} n), impossible for PRGs

There is an explicit $\varepsilon$-WPRG for standard-order permutation ROBPs of length $n$, **unbounded width** and a single accept vertex, with seed length

$$
\widetilde{O}\bigl(\log^{3/2}n\bigr)\qquad\text{for }\varepsilon=1/\mathrm{poly}(n).
$$

In contrast, Hoza, Pyne and Vadhan showed that every (unweighted) PRG for this model requires seed length $\Omega(\log^2 n)$ to achieve error $1/\mathrm{poly}(n)$, so weighted generators achieve parameters impossible for PRGs. As a corollary there are explicit WPRGs with seed length $\widetilde{O}(\log^{3/2}n)$ and error $1/\mathrm{poly}(n)$ for permutation ROBPs of width $\mathrm{poly}(n)$ with arbitrarily many accept vertices; previously seed length $o(\log^2 n)$ was known only when both the width and $1/\varepsilon$ are $n^{o(1)}$ (Braverman–Rao–Raz–Yehudayoff).

## Proof sketch

The starting point is the deterministic near-logspace Laplacian-solver algorithms of Ahmadinejad, Kelner, Murtagh, Peebles, Sidford and Vadhan for Eulerian random walks, interpreted as WPRGs with large seed length: the walk probabilities are entries of the inverse of an Eulerian Laplacian, approximated by a preconditioned Richardson iteration. Derandomizing the samples used in this iteration with the INW generator, whose error for permutation programs does not grow with the width, yields the seed $\widetilde{O}(\log^{3/2}n)$; the single accept vertex is what makes the width-independent spectral analysis apply.

## Depends on

- [Weighted pseudorandom generators (pseudorandom pseudodistributions)](weighted-pseudorandom-generators.md)
- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Proof depends on

- [Spectral approximation of graphs](../../../ComputerScience/graph-algorithms/graph-algorithm-bounds/spectral-approximation-of-graphs.md)
- [Cohen–Doron–Renard–Sberlo–Ta-Shma: black-box error reduction from PRGs to weighted PRGs via Richardson iteration](error-reduction-prg-to-weighted-prg.md)

## Sources

- Edward Pyne and Salil Vadhan, "Pseudodistributions That Beat All Pseudorandom Generators", CCC (2021); Theory of Computing 22(3) (2026), ECCC TR21-019.
- William M. Hoza, Edward Pyne and Salil Vadhan, "Pseudorandom Generators for Unbounded-Width Permutation Branching Programs", ITCS (2021), ECCC TR20-138.
- AmirMahdi Ahmadinejad, Jonathan Kelner, Jack Murtagh, John Peebles, Aaron Sidford and Salil Vadhan, "High-precision Estimation of Random Walks in Small Space", FOCS (2020), arXiv:1912.04524.
