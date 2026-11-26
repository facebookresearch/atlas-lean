# Parseval / sum-of-squares for characters

Let $G$ be a finite group and let $k$ be an algebraically closed field in which $|G|$ is invertible.
Let $(\rho_i)_{i \in I}$ be a family, indexed by a finite set $I$, of irreducible representations
of $G$ on finite-dimensional $k$-vector spaces that are pairwise non-equivalent, with characters
$\chi_{\rho_i}$. Let $n_i \in \mathbb{N}$ and $\chi = \sum_{i \in I} n_i \chi_{\rho_i}$. Then, in $k$,

$$\frac{1}{|G|} \sum_{g \in G} \chi(g)\, \chi(g^{-1}) = \sum_{i \in I} n_i^2 .$$

In particular a single irreducible character $\chi_\rho$ has self-pairing $1$, and for the regular
character, expanded in irreducible characters, the formula recovers
$\sum_i (\dim \rho_i)^2 = |G|$.

Algebraic closedness is needed: over $\mathbb{R}$, the irreducible two-dimensional rotation
representation of the cyclic group of order $3$ has character values $2, -1, -1$ and self-pairing
$2$.
