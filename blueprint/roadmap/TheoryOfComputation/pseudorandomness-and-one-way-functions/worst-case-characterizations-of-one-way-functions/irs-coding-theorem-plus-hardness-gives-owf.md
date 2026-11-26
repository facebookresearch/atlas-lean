# Ilango–Ren–Santhanam: a coding theorem plus average-case hardness of additive approximation yields one-way functions

Let $\mathcal D=\{\mathcal D_n\}$ be a polynomial-time samplable distribution family on $\{0,1\}^n$ and let $\Delta=\omega(\log n)$. Time-unbounded Kolmogorov complexity satisfies the **coding theorem** for $\mathcal D$: every $x\in\{0,1\}^n$ output by $\mathcal D_n$ with probability $p$ has $K(x)\le\log(1/p)+O(\log n)$. If approximating $K$ within an additive $\Delta$ is weakly average-case hard on $\mathcal D$, then one-way functions exist.

## Proof sketch

Suppose one-way functions do not exist. Then the probability $D(x)$ of a sample can be estimated within a constant factor on most samples (by inverting the sampler and counting preimages), and the estimate $\log(1/D(x))$ is a good approximation of $K(x)$ for most samples: the coding theorem gives $K(x)\le\log(1/D(x))+O(\log n)$, while counting shows that only a $2^{-\Delta/2}$ fraction of the mass of $D$ can sit on strings with $K(x)<\log(1/D(x))-\Delta/2$. So the estimator approximates $K$ within $\Delta$ on most of $D$, contradicting weak average-case hardness.

## Depends on

- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)

## Proof depends on

- [Few strings have small complexity](../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)
- [Stockmeyer: approximate counting of #P functions in BPP^NP](../../counting-complexity/stockmeyer-approximate-counting.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
