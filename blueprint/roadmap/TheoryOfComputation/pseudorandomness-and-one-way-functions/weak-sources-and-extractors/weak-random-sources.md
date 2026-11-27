# k-sources, (k, ε)-sources and flat sources

A distribution $p$ on a finite set $\Omega$ is a *$k$-source* if its min-entropy is at least $k$, i.e. $p(a) \le 2^{-k}$ for every $a \in \Omega$ (min-entropy in bits). It is a *$(k, \varepsilon)$-source* if it is within statistical distance $\varepsilon$ of some $k$-source. A *flat source* is the uniform distribution on a nonempty subset of $\Omega$; the uniform distribution on a set of $K$ outcomes has min-entropy $\log_2 K$. Mixtures of $k$-sources are $k$-sources, and a $(k, 0)$-source is a $k$-source.

## Depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)
- [Total variation distance of functions on a finite set](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 230–261, 1988.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012, Definitions 6.2 and 6.9.
