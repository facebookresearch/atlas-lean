# Support inclusion and Umegaki relative entropy

For $\rho,\sigma \in M_\iota(\mathbb{C})$ say that the support of $\rho$ is contained in that of $\sigma$, written $\operatorname{supp}\rho \subseteq \operatorname{supp}\sigma$, if $\ker\sigma \subseteq \ker\rho$. For positive semidefinite $\rho, \sigma$ (not necessarily normalized) the *Umegaki relative entropy* in nats is the extended real number

$$
D(\rho\,\|\,\sigma) = \begin{cases} \operatorname{Tr}\big(\rho(\log\rho - \log\sigma)\big) & \text{if } \operatorname{supp}\rho \subseteq \operatorname{supp}\sigma, \\ +\infty & \text{otherwise,} \end{cases}
$$

where $\log$ is the natural logarithm applied by functional calculus with the convention $\log 0 = 0$ on kernels. Relabelling the basis by a common permutation preserves $D$, and $D(\rho\,\|\,c\sigma) = D(\rho\,\|\,\sigma) - (\log c)\operatorname{Tr}\rho$ for $c > 0$.

## Depends on

- [Density matrices, pure states and reduced states](../density-matrices-and-fidelity/density-matrices-and-reduced-states.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
