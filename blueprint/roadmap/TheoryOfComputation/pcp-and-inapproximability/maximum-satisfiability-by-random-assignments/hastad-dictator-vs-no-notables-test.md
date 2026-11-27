# Håstad's 3-query linearity test is a $(1/2, 1-\delta)$ Dictator-vs.-No-Notables test

For every $0 < \delta < 1/2$ there is a $(1/2, 1-\delta)$-Dictator-vs.-No-Notables test (soundness $1/2$, completeness $1-\delta$) using only Max-E3-Lin predicates $x_1 x_2 x_3 = \pm 1$ (equivalently, $x_1 \oplus x_2 \oplus x_3 = b$): choose $x, y$ uniformly and a uniform sign $b$, let $z$ be $b\,xy$ with each coordinate flipped independently with probability $\delta$, and check $f(x) f(y) f(z) = b$. Dictators pass with probability $1 - \delta$, while every function with no $(\varepsilon,\varepsilon)$-notable coordinates, $\varepsilon\le2\delta$, passes with probability at most $1/2 + \sqrt{\varepsilon}/2$. Håstad's optimal inapproximability of Max-E3-Lin is proved with a more elaborate variant of this test.

## Proof sketch

The acceptance probability equals $\tfrac12 + \tfrac12 \sum_{|S|\text{ odd}} (1-2\delta)^{|S|} \hat f(S)^3$ (the random sign $b$ cancels the even-size terms, including $S=\emptyset$); for a dictator this is $1-\delta$. If $\mathrm{Inf}_i^{(1-\varepsilon)}[f]=\sum_{S\ni i}(1-\varepsilon)^{|S|-1}\hat f(S)^2\le\varepsilon$ for all $i$ and $\varepsilon\le2\delta$, then for every nonempty $S$ we get $(1-2\delta)^{2|S|}\hat f(S)^2\le\varepsilon$, so the odd-size sum is at most $\sqrt{\varepsilon}\sum_S\hat f(S)^2=\sqrt{\varepsilon}$ by Parseval. In O'Donnell's notation this is the Håstad$_{2\delta}$ test, whose noise $N_{1-2\delta}$ flips each coordinate with probability $\delta$.

## Depends on

- [Dictator-vs.-No-Notables tests](dictator-vs-no-notables-tests.md)

## Proof depends on

- [Satisfaction probability at a randomized assignment is the multilinear expansion](satisfaction-probability-multilinear-expansion.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 798–859, 2001.
- R. O'Donnell, Analysis of Boolean Functions, Cambridge University Press, 2014, Theorem 7.42 and its proof.
