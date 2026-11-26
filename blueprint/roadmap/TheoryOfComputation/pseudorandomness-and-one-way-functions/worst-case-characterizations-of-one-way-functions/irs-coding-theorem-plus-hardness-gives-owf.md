# Ilango–Ren–Santhanam: a coding theorem plus average-case hardness of additive approximation yields one-way functions

Let $C$ be a complexity measure on strings that is suitably well behaved (for instance $K$ or time-bounded variants) and let $\mathcal S$ be a class of polynomial-time samplable distributions satisfying a **coding theorem**: every $x\in\{0,1\}^n$ output with probability $p$ by some $D\in\mathcal S$ satisfies $C(x)\le\log(1/p)+O(\log n)$. Let $\Delta=\omega(\log n)$. If for some $D\in\mathcal S$ it is weakly average-case hard to approximate $C$ within an additive $\Delta$ on $D$, then one-way functions exist.

## Proof sketch

Suppose one-way functions do not exist. Then the probability $D(x)$ of a sample can be estimated within a constant factor on most samples (by inverting the sampler and counting preimages), and the estimate $\log(1/D(x))$ is a good approximation of $C(x)$ for most samples: the coding theorem gives $C(x)\le\log(1/D(x))+O(\log n)$, while counting shows that only a $2^{-\Delta/2}$ fraction of the mass of $D$ can sit on strings with $C(x)<\log(1/D(x))-\Delta/2$. So the estimator approximates $C$ within $\Delta$ on most of $D$, contradicting weak average-case hardness.

## Depends on

- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Few strings have small complexity](../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)
- [Stockmeyer: approximate counting of #P functions in BPP^NP](../../counting-complexity/stockmeyer-approximate-counting.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
