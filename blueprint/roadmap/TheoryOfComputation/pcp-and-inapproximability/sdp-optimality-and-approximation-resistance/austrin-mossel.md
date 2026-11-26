# Austrin–Mossel: pairwise independence implies UG-approximation resistance

Assume the Unique Games Conjecture. Let $P \subseteq [q]^k$ be a predicate such that some balanced pairwise independent distribution $\mu$ on $[q]^k$ has $\operatorname{supp}(\mu) \subseteq P$. Then $P$ is approximation resistant. In particular, for $q = 2$ and $k = 2^t - 1$ the predicate given by the support of the Hadamard code is resistant, so Max-$k$-CSP over the Boolean domain is UG-hard to approximate within a factor $O(k/2^k)$.

## Proof sketch

Use a dictatorship test that samples $R$ independent copies of $\mu$ with small noise and checks $P$. Dictators pass with probability close to $1$. For low-influence functions, pairwise independence implies that all degree-two correlations vanish, so by the invariance principle the acceptance probability is close to that of independent Gaussians, which equals the density $\rho(P)$ after the standard folding.

## Depends on

- [Approximation-resistant predicates and balanced pairwise independence](approximation-resistance.md)
- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Proof depends on

- [Dictatorship tests compose with Unique Games to give hardness](dictatorship-to-ug-hardness.md)

## Sources

- P. Austrin, E. Mossel, "Approximation resistant predicates from pairwise independence", Computational Complexity 18 (2009) 249-271, arXiv:0802.2300.
- E. Mossel, R. O'Donnell, K. Oleszkiewicz, "Noise stability of functions with low influences: invariance and optimality", Annals of Mathematics 171 (2010) 295-341.
