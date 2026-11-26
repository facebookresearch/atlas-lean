# Impagliazzo's hard-core lemma

A *measure* on $\{0,1\}^n$ is a function $\mu:\{0,1\}^n\to[0,1]$ of density $|\mu|/2^n$ where $|\mu|=\sum_x\mu(x)$. There is a polynomial $p$ such that the following holds. Let $f:\{0,1\}^n\to\{0,1\}$ be $\delta$-hard for size $s$, and let $0<\varepsilon<1$. Then there is a measure $\mu$ of density at least $\delta$ that is *hard-core*: every function $g$ of circuit complexity at most $s'=\varepsilon^2\delta^2 s/p(n)$ satisfies $\sum_{x:\,g(x)=f(x)}\mu(x)\le(\tfrac12+\varepsilon)|\mu|$. Equivalently (after rounding), there is a set $H$ of at least $\delta 2^n$ inputs on which every circuit of size $s'$ computes $f$ correctly with probability at most $\tfrac12+\varepsilon$.

## Proof sketch

Otherwise, for every dense measure some small circuit has advantage $\varepsilon$ on it; by the min-max theorem (or boosting) a distribution over small circuits has advantage on every dense measure, and a majority vote of $O(\varepsilon^{-2}\log(1/\delta))$ samples from it computes $f$ on all but a $\delta$ fraction of inputs, contradicting $\delta$-hardness.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Sources

- Russell Impagliazzo, "Hard-Core Distributions for Somewhat Hard Problems", Proceedings of the 36th Annual Symposium on Foundations of Computer Science, 1995.
- Thomas Holenstein, "Key Agreement from Weak Bit Agreement", Proceedings of the Thirty-Seventh Annual ACM Symposium on Theory of Computing, 2005.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
