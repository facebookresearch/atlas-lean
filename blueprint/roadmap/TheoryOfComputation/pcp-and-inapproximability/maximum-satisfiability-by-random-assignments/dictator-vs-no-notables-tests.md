# Dictator-vs.-No-Notables tests

Let $\Psi$ be a finite set of predicates over $\{-1,1\}$, let $0<\alpha<\beta\le1$, and let $\lambda:[0,1]\to[0,1]$ satisfy $\lambda(\varepsilon)\to0$ as $\varepsilon\to0$. Suppose that for each $n$ there is a local tester for functions $f:\{-1,1\}^n\to\{-1,1\}$ that queries $f$ at random strings and accepts or rejects by applying a predicate from $\Psi$ to the answers, so that the tester is an instance of $\mathrm{Max}$-$\mathrm{CSP}(\Psi)$ whose variables are the $2^n$ points of the cube. If every dictator $f(x)=x_i$ is accepted with probability at least $\beta$, and every $f$ with no $(\varepsilon,\varepsilon)$-notable coordinates, that is, with stable influences $\mathrm{Inf}_i^{(1-\varepsilon)}[f]\le\varepsilon$ for all $i$, is accepted with probability at most $\alpha+\lambda(\varepsilon)$, the family is an $(\alpha,\beta)$-*Dictator-vs.-No-Notables test* using $\Psi$. The first parameter is the soundness and the second the completeness; the error term $\lambda$ must not depend on $n$.

## Depends on

- [Maximum constraint satisfaction problems](maximum-constraint-satisfaction-problems.md)
- [Stable influence and total stable influence](../../../Combinatorics/boolean-functions/noise-sensitivity-and-stable-influence/stable-influence.md)

## Sources

- R. O'Donnell, Analysis of Boolean Functions, Cambridge University Press, 2014, Definition 7.37 and Definition 6.9.
- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 798–859, 2001.
