# Lipton: random self-reducibility of the permanent

Let $p>n+1$ be prime. There is a randomized algorithm that computes $\operatorname{perm}(M)\bmod p$ for every $M\in\mathbb{F}_p^{n\times n}$ by querying an oracle $O$ on $n+1$ matrices, each individually uniformly distributed over $\mathbb{F}_p^{n\times n}$; if $O$ agrees with the permanent on all but a $\frac{1}{3(n+1)}$ fraction of matrices, the algorithm is correct with probability at least $2/3$.

## Proof sketch

Choose a uniformly random $R$ and query $O(M+iR)$ for $i=1,\dots,n+1$. The univariate polynomial $t\mapsto\operatorname{perm}(M+tR)$ has degree $\le n$, so interpolation from the $n+1$ answers gives its value at $t=0$; each query point is uniform, and a union bound bounds the error.

## Depends on

- [The 0-1 permanent counts perfect matchings](../complexity-of-the-permanent/permanent-boole-eq-card.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
