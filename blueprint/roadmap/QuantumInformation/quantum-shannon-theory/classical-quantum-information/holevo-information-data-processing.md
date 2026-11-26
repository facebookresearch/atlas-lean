# Data processing for Holevo information

Let $(p,\rho)$ be a finite ensemble on $\mathbb{C}^\iota$ and $\Phi(Y) = \sum_j K_j Y K_j^*$ a channel with Kraus operators $K_j:\mathbb{C}^\iota\to\mathbb{C}^{\iota'}$, $\sum_j K_j^*K_j = I$. Then $\chi\big(p, (\Phi(\rho_x))_x\big)\le\chi(p,\rho)$.

## Proof sketch

Holevo information is $(\ln 2)^{-1}$ times the relative entropy of the classical-quantum state to the product of its marginals. Applying $\Phi\otimes\mathrm{id}$ maps both states to the corresponding states of the processed ensemble, and this map is again a Kraus channel, so data processing for relative entropy gives the inequality.

## Depends on

- [Von Neumann entropy and Holevo information](von-neumann-entropy-and-holevo-information.md)
- [Finite-family Kraus linear map](../../../Analysis/not-yet-classified/kraus/kraus-linear-map.md)

## Proof depends on

- [Holevo information as classical-quantum mutual information and its bounds](holevo-information-properties.md)
- [Data processing for quantum relative entropy under Kraus channels](../../quantum-states-distances-and-entropy/quantum-relative-entropy/relative-entropy-kraus-data-processing.md)

## Sources

- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
