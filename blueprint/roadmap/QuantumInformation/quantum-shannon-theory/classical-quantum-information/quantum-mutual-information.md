# Quantum mutual information

For a density matrix $\rho_{AB}$ on $\mathbb{C}^\iota\otimes\mathbb{C}^\kappa$ with reduced states $\rho_A = \operatorname{Tr}_B\rho_{AB}$ and $\rho_B = \operatorname{Tr}_A\rho_{AB}$, the *quantum mutual information* in nats is

$$
I(A:B)_\rho = D(\rho_{AB}\,\|\,\rho_A\otimes\rho_B),
$$

the Umegaki relative entropy to the product of the marginals. It is always finite and nonnegative, and for diagonal (classical) $\rho_{AB}$ it equals the Shannon mutual information of the joint distribution.

## Depends on

- [Support inclusion and Umegaki relative entropy](../../quantum-states-distances-and-entropy/quantum-relative-entropy/umegaki-relative-entropy.md)
- [Mutual information of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
