# Classical query lower bound from list recoverability

If $C$ is $(\zeta, \ell, L)$-list recoverable for a constant $\zeta > 0$, with list parameter $\ell \ge T$ and $L \le 2^{o(n)}$, then every classical algorithm making $T$ queries to $H$ solves $\mathrm{YZ}^H_C$ with probability at most $\mathrm{poly}(T) \cdot 2^{-\Omega(n)}$ over $H$ and its coins.

## Proof sketch

A classical algorithm's knowledge after $T$ queries is a set of queried points per coordinate. Any output codeword must have, at coordinates where its symbol was not queried, a fresh fair coin satisfied, costing a factor $1/2$ per such coordinate. If many coordinates are queried, the queried symbols per coordinate form lists, and list recoverability bounds the number of codewords consistent with mostly-queried lists by $L$, each of which still has an independent probability of satisfying the remaining coordinates; a union bound gives the estimate.

## Depends on

- [The Yamakawa-Zhandry codeword search problem](yamakawa-zhandry-codeword-search-problem.md)
- [List-recoverable codes](list-recoverable-codes-for-oracle-hardness.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
