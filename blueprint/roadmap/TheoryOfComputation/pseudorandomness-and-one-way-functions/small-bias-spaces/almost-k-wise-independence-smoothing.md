# k-wise small bias is close to exact k-wise independence

Let $X$ be a distribution on $\{0,1\}^n$ and $k \ge 1$. If $X$ is $k$-wise $\varepsilon$-biased, then there is a $k$-wise independent distribution $X'$ on $\{0,1\}^n$ (every $k$ coordinates exactly uniform) with $\Delta(X, X') \le B/(1+B) \le n^k \varepsilon$, where $B = \sum_{0 < |S| \le k} |\mathrm{bias}_X(S)| \le n^k \varepsilon$. Conversely, if every marginal of $X$ on at most $k$ coordinates is within statistical distance $\gamma$ of uniform, then $X$ is $k$-wise $2\gamma$-biased.

## Proof sketch

Subtract from the mass function its low-degree Fourier part $2^{-n}\sum_{0<|S|\le k} \mathrm{bias}_X(S)\chi_S$, mix with the uniform distribution to restore nonnegativity, and renormalize; the perturbation has $\ell_1$ mass at most $B$. There are at most $n^k$ nonempty sets of size at most $k$. The converse holds because a parity is a $\{0,1\}$-valued test.

## Depends on

- [Bias, ε-biased and k-wise ε-biased distributions](small-bias-distributions.md)
- [Total variation distance of functions on a finite set](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms, 1992.
- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics, 2019.
