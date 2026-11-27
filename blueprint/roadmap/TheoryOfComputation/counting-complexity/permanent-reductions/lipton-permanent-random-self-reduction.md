# Lipton: random self-reducibility of the permanent

Let $\mathbb{F}$ be a finite field with $|\mathbb{F}|>3n$. There is a randomized algorithm that, given an oracle that computes the permanent correctly on a $1-\frac{1}{3n}$ fraction of the matrices in $\mathbb{F}^{n\times n}$, computes $\operatorname{perm}(A)$ correctly for every $A\in\mathbb{F}^{n\times n}$ with high probability. It picks a uniformly random $R\in\mathbb{F}^{n\times n}$ and queries the oracle on the $n+1$ matrices $A+iR$ for $i=1,\dots,n+1$, each of which is individually uniformly distributed.

## Proof sketch

The univariate polynomial $t\mapsto\operatorname{perm}(A+tR)$ has degree at most $n$, so interpolation from the $n+1$ answers gives its value at $t=0$; each query point is uniform, so a union bound shows that all $n+1$ answers are correct with probability at least $1-\frac{n+1}{3n}\approx\frac23$.

Derived here (not stated in the cited source in this form): over $\mathbb{F}_p$ with $p>n+1$ prime, if the oracle agrees with the permanent on all but a $\frac{1}{3(n+1)}$ fraction of matrices, the same algorithm is correct with probability at least $2/3$, since the points $1,\dots,n+1$ are distinct and nonzero and the union bound gives failure probability at most $\frac{n+1}{3(n+1)}=\frac13$.

## Depends on

- [The 0-1 permanent counts perfect matchings](../complexity-of-the-permanent/permanent-boole-eq-card.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009; web draft of January 2007, Appendix 8.A, Theorem 8.30 (Lipton) and its proof.
