# Impagliazzo's hard-core lemma

A *measure* on $\{0,1\}^n$ is a function $\mu:\{0,1\}^n\to[0,1]$ of density $|\mu|/2^n$ where $|\mu|=\sum_x\mu(x)$. Let $0<\delta<\tfrac12$, $0<\varepsilon<1$ and $s\le 2^n/n$, and let $f:\{0,1\}^n\to\{0,1\}$ be $\delta$-hard for size $s$. Then there is a measure $\mu$ of density at least $\delta$ that is *$\varepsilon$-hard-core* for size $s'=\tfrac14\varepsilon^2\delta^2 s$: every function $g$ of circuit complexity at most $s'$ satisfies

$$
\sum_{x:\,g(x)=f(x)}\mu(x)-\sum_{x:\,g(x)\ne f(x)}\mu(x)<\varepsilon|\mu|,
$$

that is, $g$ agrees with $f$ with probability less than $\tfrac12(1+\varepsilon)$ under the distribution induced by $\mu$. Consequently (choosing a random set with $\Pr[x\in H]=\mu(x)$) there is a set $H$ of at least $\delta 2^n$ inputs on which every circuit of size at most $d\,\varepsilon^2\delta^2s$, for an absolute constant $d>0$, agrees with $f$ with probability less than $\tfrac12(1+\varepsilon)$. Holenstein improved the density of the hard-core measure to the optimal $2\delta$.

## Proof sketch

Otherwise, for every measure of density at least $\delta$ some circuit of size $s'$ has advantage $\varepsilon$ on it. Impagliazzo's boosting argument builds measures $M_0,M_1,\dots$, each downweighting inputs on which the majority of the circuits found so far is already comfortably correct, and stops after $O(1/(\varepsilon^2\delta^2))$ rounds with a majority vote of circuits of total size below $s$ that computes $f$ on all but a $\delta$ fraction of inputs, contradicting $\delta$-hardness. (Nisan's alternative proof uses the min-max theorem and a majority of $O(\varepsilon^{-2}\log(1/\delta))$ samples.)

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Sources

- Russell Impagliazzo, "Hard-Core Distributions for Somewhat Hard Problems", Proceedings of the 36th Annual Symposium on Foundations of Computer Science (FOCS 1995), 1995 (Lemma 1 and Theorem 1).
- Thomas Holenstein, "Key Agreement from Weak Bit Agreement", Proceedings of the Thirty-Seventh Annual ACM Symposium on Theory of Computing (STOC 2005), 2005 (hard-core lemma with optimal density).
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (Impagliazzo's hardcore lemma; Lemma 17.5 in the 2007 web draft, density $\delta/2$ for circuits of size $\varepsilon^2S/(100\log(1/\delta))$).
