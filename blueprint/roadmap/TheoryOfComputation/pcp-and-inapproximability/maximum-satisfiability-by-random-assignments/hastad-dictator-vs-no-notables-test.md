# Håstad's 3-query linearity test is a $(1/2, 1-\delta)$ Dictator-vs.-No-Notables test

For every $0 < \delta < 1/2$ there is a $(1-\delta, 1/2)$-Dictator-vs.-No-Notables test using only Max-E3-Lin predicates $x_1 x_2 x_3 = \pm 1$ (equivalently, $x_1 \oplus x_2 \oplus x_3 = b$): choose $x, y$ uniformly, $z$ by flipping each coordinate of $xy$ independently with probability $\delta$, and check $f(x) f(y) f(z) = 1$. Dictators pass with probability $1 - \delta$, while every function without notable coordinates passes with probability at most $1/2 + \varepsilon$. Via the label-cover framework this yields Håstad's optimal inapproximability of Max-E3-Lin.

## Proof sketch

The acceptance probability equals $\tfrac12 + \tfrac12 \sum_S (1-2\delta)^{|S|} \hat f(S)^3$; for a dictator this is $1-\delta$, and when all low-degree influences are small, $\max_S (1-2\delta)^{|S|}|\hat f(S)|$ is small, so the cubic sum is at most $\varepsilon$ by Parseval.

## Depends on

- [Dictator-vs.-No-Notables tests](dictator-vs-no-notables-tests.md)

## Proof depends on

- [Satisfaction probability at a randomized assignment is the multilinear expansion](satisfaction-probability-multilinear-expansion.md)
- [Hastad: optimal inapproximability of MAX-3SAT](../approximability-of-max-3sat/hastad-max3sat-inapproximability.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 798–859, 2001.
- R. O'Donnell, Analysis of Boolean Functions, Cambridge University Press, 2014.
