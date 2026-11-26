# Multiparty discrepancy

For $f : \prod_i X_i \to \{0,1\}$ and a distribution $\nu$ on inputs, the *multiparty discrepancy* is

$$\mathrm{disc}^{k}_\nu(f) = \max_{C} \Big| \sum_{x \in C} \nu(x) (-1)^{f(x)} \Big|,$$

the maximum over cylinder intersections $C$. As in the two-party case, a public-coin NOF protocol of cost $c$ computing $f$ with error at most $1/2 - \gamma$ satisfies $2\gamma \le 2^c\, \mathrm{disc}^k_\nu(f)$.

## Depends on

- [Number-on-forehead protocols and cylinder intersections](number-on-forehead-protocols.md)
- [Discrepancy of a function under a distribution](../discrepancy-corruption-and-sign-rank/discrepancy-under-a-distribution.md)

## Sources

- L. Babai, N. Nisan and M. Szegedy, "Multiparty Protocols, Pseudorandom Generators for Logspace, and Time-Space Trade-offs", Journal of Computer and System Sciences 45(2), 1992.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
