# Gaifman locality of first-order formulas

Let $\varphi(\bar x)$ be a first-order formula of quantifier rank $n$ and $\mathfrak{A}$ a finite structure. If $\bar a, \bar b$ are tuples of $\mathfrak{A}$ with isomorphic $r$-neighborhoods for $r = (3^{n+1} - 1)/2$, then $\mathfrak{A} \models \varphi(\bar a) \iff \mathfrak{A} \models \varphi(\bar b)$. Thus every first-order query is *Gaifman-local*: its value on a tuple depends only on the isomorphism type of a neighborhood of bounded radius.

## Proof sketch

With $d = (3^n - 1)/2$ the Hanf radius of rank-$n$ formulas, $r = 3d + 1$. Isomorphic $(3d+1)$-neighborhoods of $\bar a$ and $\bar b$ inside one structure yield $(\mathfrak{A}, \bar a) \leftrightarrows_d (\mathfrak{A}, \bar b)$, by the isomorphism near the tuples and a type-preserving matching of the remaining elements; apply Hanf locality.

## Depends on

- [Gaifman graphs, distance and neighborhoods](gaifman-graphs-and-neighborhoods.md)

## Proof depends on

- [Hanf locality of first-order logic](hanf-locality.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004: Lemma 4.9, Theorem 4.11 and Corollary 4.13.
- L. Hella, L. Libkin and J. Nurmonen, "Notions of Locality and Their Logical Characterizations over Finite Models", Journal of Symbolic Logic 64(4), 1751–1773, 1999.
