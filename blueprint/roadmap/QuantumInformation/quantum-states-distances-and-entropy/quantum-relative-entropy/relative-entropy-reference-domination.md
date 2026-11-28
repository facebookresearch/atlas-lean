# Relative entropy under domination of the reference

Let $\rho$ be a density matrix and $\sigma,\tau$ positive semidefinite (possibly singular or unnormalized).

1. If $\sigma\le\tau$ in the Loewner order then $D(\rho\,\|\,\tau)\le D(\rho\,\|\,\sigma)$; this holds for every positive semidefinite $\rho$.
2. If $\sigma\le c\,\tau$ for some $c>0$ then $D(\rho\,\|\,\tau)\le D(\rho\,\|\,\sigma) + \log c$.
3. If $\sigma_1,\dots,\sigma_m$ are positive semidefinite, $w_j\ge 0$, $\sigma_k$ is a density matrix and $w_k>0$, then $D\big(\sigma_k\,\|\,\sum_j w_j\sigma_j\big) \le -\log w_k$, whatever the total weight.

## Proof sketch

For part 1, $\sigma\le\tau$ forces $\ker\tau\subseteq\ker\sigma$, and the resolvent objective is pointwise decreasing in the reference, so $R_t(\rho,\tau)\le R_t(\rho,\sigma)$ for all $t$; integrate. Part 2 applies part 1 to $c\tau$ and uses $D(\rho\|c\tau) = D(\rho\|\tau) - \log c$. Part 3 applies part 2 to $w_k\sigma_k \le \sum_j w_j\sigma_j$ together with $D(\sigma_k\|\sigma_k) = 0$.

## Depends on

- [Density matrices, pure states and reduced states](../density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)

## Proof depends on

- [Integral representation of relative entropy by the resolvent kernel](relative-entropy-resolvent-integral.md)
- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
