# Gaifman locality of first-order formulas

Let $\varphi(\bar x)$ be a first-order formula of quantifier rank $n$ and $\mathfrak{A}$ a finite structure. If $\bar a, \bar b$ are tuples of $\mathfrak{A}$ with isomorphic $r$-neighborhoods for $r = (3^{n+1} - 1)/2$, then $\mathfrak{A} \models \varphi(\bar a) \iff \mathfrak{A} \models \varphi(\bar b)$. Thus every first-order query is *Gaifman-local*: its value on a tuple depends only on the isomorphism type of a neighborhood of bounded radius.

## Proof sketch

Isomorphic neighborhoods of radius $3r+1$ inside one structure yield Hanf equivalence of $(\mathfrak{A}, \bar a)$ and $(\mathfrak{A}, \bar b)$ at radius $r$ by matching the complement of the balls identically; apply Hanf locality.

## Depends on

- [Gaifman graphs, distance and neighborhoods](gaifman-graphs-and-neighborhoods.md)

## Proof depends on

- [Hanf locality of first-order logic](hanf-locality.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
