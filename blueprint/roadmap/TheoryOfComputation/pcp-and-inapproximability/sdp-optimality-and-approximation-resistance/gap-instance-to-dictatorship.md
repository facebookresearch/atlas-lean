# From SDP integrality gaps to dictatorship tests

Let $\Im$ be an instance of $\mathrm{GCSP}(\Lambda)$ with $\operatorname{sdp}(\Im) \ge c$ and $\operatorname{opt}(\Im) \le s$. Then for every $\eta > 0$ there are $\tau, d > 0$ and a dictatorship test $\mathcal{T}_\Im$ for $\mathrm{GCSP}(\Lambda)$ with completeness at least $c - \eta$ and $(\tau, d)$-soundness at most $s + \eta$.

## Proof sketch

The test picks a random constraint $(P, v)$ of $\Im$, samples $R$ independent copies of the local distribution $\mu_{P,v}$ (perturbed by a little noise) to produce correlated query points, and checks $P$. Dictators achieve the SDP value of $\Im$. For low-influence functions, the invariance principle replaces the discrete local distributions by Gaussians with the same second moments, which are exactly the SDP vectors, so a low-influence $F$ yields a rounding of the SDP solution to an integral assignment of $\Im$ of value close to $\mathcal{T}(F)$, which is at most $s$.

## Depends on

- [Dictatorship tests and their completeness and soundness](dictatorship-test.md)
- [The integrality gap curve of the basic SDP](integrality-gap-curve.md)
- [The basic SDP relaxation of a generalized CSP](basic-sdp-relaxation.md)
- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)

## Proof depends on

- [Majority Is Stablest](../../../Combinatorics/boolean-functions/structure-theorems-for-boolean-functions/majority-is-stablest.md)

## Sources

- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
- E. Mossel, R. O'Donnell, K. Oleszkiewicz, "Noise stability of functions with low influences: invariance and optimality", Annals of Mathematics 171 (2010) 295-341.
