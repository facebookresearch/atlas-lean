# k-wise small bias is close to exact k-wise independence

Let $X$ be a distribution on $\{0,1\}^n$ and $k \ge 1$. If $X$ is $k$-wise $\varepsilon$-biased, then there is a $k$-wise independent distribution $X'$ on $\{0,1\}^n$ (every $k$ coordinates exactly uniform) with $\Delta(X, X') \le B/(1+B) \le n^k \varepsilon$, where $B = \sum_{0 < |S| \le k} |\mathrm{bias}_X(S)| \le n^k \varepsilon$. Conversely, if every marginal of $X$ on at most $k$ coordinates is within statistical distance $\gamma$ of uniform, then $X$ is $k$-wise $2\gamma$-biased.

## Proof sketch

Let $g=2^{-n}\sum_{0<|S|\le k} \mathrm{bias}_X(S)\chi_S$, so $|g|\le 2^{-n}B$ pointwise and $\sum_x g(x)=0$. Then $X'=(\mu_X-g+B\,2^{-n})/(1+B)$ is a probability distribution with zero bias on every nonempty set of size at most $k$, and $X'-\mu_X=(h-B\mu_X)/(1+B)$ for the nonnegative $h=B2^{-n}-g$ of total mass $B$, so $\Delta(X,X')\le B/(1+B)$. There are at most $n^k$ nonempty sets of size at most $k$. The converse holds because a parity is a $\{0,1\}$-valued test.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Total variation distance of functions on a finite set](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- N. Alon, O. Goldreich and Y. Mansour, "Almost k-wise Independence versus k-wise Independence", Information Processing Letters 88(3), 107–110, 2003 (the smoothing argument and the $n^k\varepsilon$ bound).
- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 289–304, 1992.
- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019.
