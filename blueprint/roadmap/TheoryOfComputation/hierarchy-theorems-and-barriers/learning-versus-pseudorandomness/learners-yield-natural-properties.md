# Oliveira-Santhanam: learners for SIZE(s) yield P/poly-natural properties useful against SIZE(s)

For a membership-query learner $A$ on $n$ coordinates with uniform seeds from a finite set $\Omega$ and a threshold $\theta$, the low-agreement property is the set of functions $g$ with $\mathbb{E}_{\omega}\Pr_z[A_\omega(g)(z) = g(z)] < \theta$. Suppose that for some constant $c$ and all $n$: $|\Omega_n| \le 2^{c(n+1)}$; $A_n$ has circuit tests of size at most $2^{c(n+1)}$ with $q_n$ queries; for all large $n$, $A_n$ learns the functions with circuits of at most $s(n)$ gates with error $\varepsilon_n \in [0,1]$ and confidence $1 - \delta_n$; and

$$
(1-\delta_n)(1-\varepsilon_n) - \Big(\frac12 + \frac{q_n}{2^{n+1}}\Big) \ge 2^{-cn}
$$

for all large $n$. Then with $\theta_n = (1-\delta_n)(1-\varepsilon_n)$ the low-agreement property is natural (decidable from truth tables by circuits of size polynomial in $2^n$, and holding for at least a $2^{-O(n)}$ fraction of functions) and useful against $\mathrm{SIZE}(s)$ (no function of circuit size at most $s(n)$ has it, for large $n$).

## Proof sketch

Members of the class have average agreement at least $\theta$ by the learning guarantee, so they lack the property. A random function has expected agreement at most $\frac12 + q/2^{n+1}$, so by an averaging argument at least a $\theta - p \ge 2^{-cn}$ fraction of functions has agreement below $\theta$. The property is a threshold of $|\Omega|2^n$ circuit tests, computable with $2^{O(n)}$ gates.

## Depends on

- [Learners computed by small circuits, with adaptive or non-adaptive membership queries](../../circuit-complexity/learning-under-the-uniform-distribution/learners-computed-by-small-circuits.md)
- [Natural property](../natural-proofs-barrier/natural-property.md)
- [Usefulness against P/poly](../natural-proofs-barrier/useful-against-ppoly.md)

## Proof depends on

- [A membership-query learner for a keyed family distinguishes it from random functions](learners-distinguish-pseudorandom-functions.md)

## Sources

- Igor Carboni Oliveira and Rahul Santhanam, "Conspiracies Between Learning Algorithms, Circuit Lower Bounds, and Pseudorandomness", 32nd Computational Complexity Conference (CCC 2017), LIPIcs 79, 2017.
