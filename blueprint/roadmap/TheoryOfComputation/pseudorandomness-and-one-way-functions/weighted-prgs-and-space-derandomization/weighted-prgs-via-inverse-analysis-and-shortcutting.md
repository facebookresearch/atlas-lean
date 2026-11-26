# Chen–Hoza–Lyu–Tal–Wu: weighted PRGs with seed Õ(log n · sqrt(log(1/ε)) + log(1/ε)) via shortcut graphs

There are explicit $\varepsilon$-WPRGs with seed length

$$
\widetilde{O}\Bigl(\log n\cdot\sqrt{\log(1/\varepsilon)}+\log(1/\varepsilon)\Bigr)
$$

for each of the following classes of length-$n$ standard-order ROBPs: width-$3$ programs; constant-width regular programs; and unbounded-width permutation programs with a single accept vertex. The best explicit unweighted PRGs for these models have seed $\widetilde{O}(\log n\cdot\log(1/\varepsilon))$, so the WPRGs are superior for small $\varepsilon$; for permutation programs they improve on Pyne–Vadhan whenever $\varepsilon\gg 1/n$, since that seed carries an extra additive $\log^{3/2}n$ term. The framework also yields a simpler proof of the Ahmadinejad–Kelner–Murtagh–Peebles–Sidford–Vadhan Eulerian random-walk estimation theorem, avoiding fast-Laplacian-solver machinery.

## Proof sketch

The error-reduction framework analyzes the inverse of the random-walk operator rather than its powers ("inverse analysis") and organizes Richardson-type corrections along shortcut graphs, combinatorial structures that let a walk of length $n$ be approximated by few long jumps of bounded hop count. Fooling each jump with a moderate-error generator and combining jumps along shortcut graphs of depth about $\sqrt{\log(1/\varepsilon)}$ balances the two seed terms; singular value approximation supplies the spectral notion preserved under these compositions.

## Depends on

- [Weighted pseudorandom generators (pseudorandom pseudodistributions)](weighted-pseudorandom-generators.md)
- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Proof depends on

- [Spectral approximation of graphs](../../../ComputerScience/graph-algorithms/graph-algorithm-bounds/spectral-approximation-of-graphs.md)
- [Cohen–Doron–Renard–Sberlo–Ta-Shma: black-box error reduction from PRGs to weighted PRGs via Richardson iteration](error-reduction-prg-to-weighted-prg.md)

## Sources

- Lijie Chen, William M. Hoza, Xin Lyu, Avishay Tal and Hongxun Wu, "Weighted Pseudorandom Generators via Inverse Analysis of Random Walks and Shortcutting", FOCS (2023), ECCC TR23-114.
