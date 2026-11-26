# Dictator-vs.-No-Notables tests

A *test* for Boolean functions $f : \{-1,1\}^n \to \{-1,1\}$ picks one of finitely many checks uniformly at random, each consisting of query strings and a predicate from a fixed family $\Psi$; it accepts $f$ when the predicate holds of the answers. It is an $(\alpha, \beta)$-*Dictator-vs.-No-Notables test* using $\Psi$ if every dictator $f(x) = x_i$ is accepted with probability at least $\alpha$, and for every $\varepsilon > 0$ there are $\delta, k$ such that every $f$ with no coordinate of $\delta$-small $k$-degree influence (no notable coordinate) is accepted with probability at most $\beta + \varepsilon$. Such a test is a CSP instance whose variables are the $2^n$ points of the cube.

## Depends on

- [Maximum constraint satisfaction problems](maximum-constraint-satisfaction-problems.md)

## Sources

- R. O'Donnell, Analysis of Boolean Functions, Cambridge University Press, 2014.
- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 798–859, 2001.
