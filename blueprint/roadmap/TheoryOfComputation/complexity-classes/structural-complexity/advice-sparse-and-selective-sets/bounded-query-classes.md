# Bounded-query oracle classes and P^{NP[O(log n)]}

For an oracle $A$ and a query bound $r(n)$, a function is computable in polynomial time with $r$ queries to $A$ if a polynomial-time oracle machine computes it while asking at most $r(|x|)$ (adaptive) membership queries to $A$. $\mathsf{P}^{\mathsf{NP}[O(\log n)]}$ is the class of languages decided this way with $O(\log n)$ queries to some $A\in\mathsf{NP}$. One has $\mathsf{NP}\cup\mathsf{coNP}\subseteq\mathsf{P}^{\mathsf{NP}[O(\log n)]}\subseteq\mathsf{P}^{\mathsf{NP}}\subseteq\Sigma_2^p\cap\Pi_2^p$.

## Depends on

- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [The class $\Sigma_k^p$](../../time-and-space-complexity-classes/sigma-k.md)
- [The universal levels of the polynomial hierarchy](../../time-and-space-complexity-classes/pi-k.md)

## Sources

- Larry J. Stockmeyer, "The Polynomial-Time Hierarchy", Theoretical Computer Science 3(1), 1976.
- Lane A. Hemaspaandra and Mitsunori Ogihara, "The Complexity Theory Companion", Springer, 2002.
