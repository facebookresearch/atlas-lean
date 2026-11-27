# A membership-query learner for a keyed family distinguishes it from random functions

Let $A$ be a membership-query learner on $N$ coordinates making at most $q$ queries that learns, with error $\varepsilon \le 1$ and confidence $1 - \delta$ ($\delta \ge 0$), a class containing every member $F_k$ of a keyed family of Boolean functions. For a seed $\omega$ and a point $z$, the test $T_{\omega,z}(g)$ runs $A_\omega$ on $g$ and accepts iff its hypothesis agrees with $g$ at $z$. Then there exist $\omega$ in the support of the seed distribution and $z$ with

$$
\Pr_{k}\big[T_{\omega,z}(F_k) = 1\big] - \Pr_{g}\big[T_{\omega,z}(g) = 1\big] \ge (1-\delta)(1-\varepsilon) - \frac12 - \frac{q}{2^{N+1}},
$$

where $k$ is a uniform key and $g$ a uniformly random function.

## Proof sketch

On a family member the comparison succeeds with probability at least $(1-\delta)(1-\varepsilon)$ averaged over $\omega$ and uniform $z$. On a random function, if $z$ was not queried, $g(z)$ is a fair coin independent of the hypothesis, and $z$ is queried with probability at most $q/2^N$; so success is at most $\frac12 + q/2^{N+1}$. Averaging finds a good fixed pair $(\omega, z)$.

## Depends on

- [Randomized membership-query learner as a family of decision trees](../../circuit-complexity/learning-under-the-uniform-distribution/membership-query-learner.md)

## Sources

- Leslie G. Valiant, "A Theory of the Learnable", Proceedings of the 16th Annual ACM Symposium on Theory of Computing, 1984.
- Oded Goldreich, Shafi Goldwasser and Silvio Micali, "How to Construct Random Functions", Journal of the ACM 33(4), 1986.
