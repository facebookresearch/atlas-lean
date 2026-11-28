# Quantum relative entropy as a classical divergence in the two eigenbases

Let $\rho = \sum_j \lambda_j u_j u_j^*$ and $\sigma = \sum_i \mu_i v_i v_i^*$ be spectral decompositions of density matrices with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Define distributions on index pairs by $p(j,i) = \lambda_j |\langle u_j, v_i\rangle|^2$ and $q(j,i) = \mu_i |\langle u_j, v_i\rangle|^2$. Then $p$ and $q$ are probability distributions, $D(\rho\,\|\,\sigma) = D_{\mathrm{KL}}(p\,\|\,q)$ (natural logarithm), and the Bhattacharyya coefficient satisfies $\sum_{j,i}\sqrt{p(j,i)q(j,i)} = \operatorname{Tr}(\sqrt\rho\sqrt\sigma)$.

## Proof sketch

The squared overlaps $|\langle u_j, v_i\rangle|^2$ form a doubly stochastic matrix, so both $p$ and $q$ sum to one. Evaluating $\operatorname{Tr}\rho\log\rho$ and $\operatorname{Tr}\rho\log\sigma$ in the two eigenbases gives $\sum p\log\lambda_j$ and $\sum p \log\mu_i$; support inclusion kills the terms with $\mu_i = 0$. The same expansion of $\operatorname{Tr}\sqrt\rho\sqrt\sigma$ gives the Bhattacharyya sum.

## Depends on

- [Density matrices, pure states and reduced states](../density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Kullback–Leibler divergence on a finite space](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
