# Yao's minimax principle for bounded-error and zero-error decision trees

For every $f : \{0,1\}^n \to \beta$ with finite input space: (1) for $0 < \varepsilon < 1/2$, $R_\varepsilon(f) = \max_\mu D^\mu_\varepsilon(f)$, the maximum of the distributional complexity over input distributions (both sides bounded-depth; at $\varepsilon = 0$ they both equal $D(f)$, not the expected-cost $R_0$); (2) for zero-error algorithms, with cost the expected number of executed queries,

$$R_0(f) = \max_{\mu} \min_{T} \mathbb{E}_{x \sim \mu}\big[\mathrm{cost}(T, x)\big],$$

the minimum over deterministic trees $T$ computing $f$ on every input, and both the optimal randomized algorithm and the hardest input distribution are attained.

## Proof sketch

Only finitely many deterministic trees without repeated queries matter (repeated queries never help), so the game between algorithm and input is a finite matrix game; von Neumann's minimax theorem, as in Yao's principle, gives equality and attainment.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)

## Proof depends on

- [Yao's minimax principle](../../randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- A. C.-C. Yao, "Probabilistic Computations: Toward a Unified Measure of Complexity", FOCS 1977.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
