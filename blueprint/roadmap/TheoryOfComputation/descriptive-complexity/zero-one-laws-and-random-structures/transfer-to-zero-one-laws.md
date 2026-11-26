# Transfer from almost-sure theories to zero-one laws

Let $\mu_n$ be probability distributions on the $\sigma$-structures with universe $\{0,\dots,n-1\}$ and $T$ a set of sentences each of which holds with $\mu_n$-probability tending to $1$. Then $T$ is satisfiable, and every sentence implied by $T$ holds with probability tending to $1$. If moreover $T$ is complete, then for every sentence $\varphi$ the probability $\mu_n(\varphi)$ tends to $0$ or to $1$, with limit $1$ exactly when $T \models \varphi$.

## Proof sketch

By compactness a consequence of $T$ follows from finitely many sentences of $T$, whose conjunction has probability tending to $1$ by a union bound; for complete $T$ apply this to $\varphi$ or $\neg\varphi$.

## Depends on

- [The uniform random graph $G(n, 1/2)$ and $G(n, p)$](uniform-random-graph.md)

## Proof depends on

- [Finite satisfiability](../../../Logic/first-order-logic/g-del-s-completeness-theorem/exists-model-of-consistent-finset.md)

## Sources

- R. Fagin, "Probabilities on Finite Models", The Journal of Symbolic Logic 41(1), 50–58, 1976.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
