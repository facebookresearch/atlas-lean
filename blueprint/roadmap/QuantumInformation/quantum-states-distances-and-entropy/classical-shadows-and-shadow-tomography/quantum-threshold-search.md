# Quantum threshold search

There is a measurement procedure that, given $m$ observables $0 \preceq A_1, \dots, A_m \preceq I$ and $O(\log^2 m / \varepsilon^2)$ copies of $\rho$, with probability at least $3/4$ either outputs an index $j$ with $\mathrm{Tr}(A_j\rho) \ge 1/2 - \varepsilon$, or correctly declares that $\mathrm{Tr}(A_i\rho) < 1/2$ for all $i$.

## Proof sketch

Bădescu and O'Donnell process the observables sequentially on a block of copies, measuring a smoothed threshold observable obtained from the empirical average over the copies, with randomized thresholds to control disturbance. A quantum union bound in the style of the gentle measurement lemma bounds the damage of rejecting measurements, so the first observable likely to exceed the threshold is found with logarithmic overhead per step.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)

## Proof depends on

- [Gentle measurement lemma](gentle-measurement-lemma-for-shadow-tomography.md)

## Sources

- Costin Badescu, Ryan O'Donnell, "Improved quantum data analysis", STOC (2021), TheoretiCS (2024); arXiv:2011.10908.
