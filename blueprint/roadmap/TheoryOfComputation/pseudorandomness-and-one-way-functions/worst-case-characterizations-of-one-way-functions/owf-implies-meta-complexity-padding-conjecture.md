# One-way functions secure against circuits imply the Meta-Complexity Padding Conjecture

If there exists a one-way function secure against polynomial-size circuits, then the Meta-Complexity Padding Conjecture holds. Hence the conjecture cannot be refuted without ruling out such one-way functions.

## Proof sketch

Under such a one-way function, approximating $\mathrm{dpK}^{\mathrm{poly}}$ is $\mathsf{NP}$-hard by the secret-sharing reduction underlying the main characterization, and the reduction can be chosen size-expanding by padding the $\mathsf{NP}$ instance. Since $\mathrm{Gap}_\delta(K^p\ \mathrm{vs}\ K)$ lies in promise-$\mathsf{NP}$ (a YES certificate is the short program), composing the trivial reduction to an $\mathsf{NP}$-complete problem with the padded hardness reduction gives the required size-expanding reduction.

## Depends on

- [The Meta-Complexity Padding Conjecture](meta-complexity-padding-conjecture.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Hirahara: one-way functions exist iff approximating distributional Kolmogorov complexity is NP-hard and NP is worst-case hard](hirahara-owf-iff-np-hardness-of-dk.md)

## Sources

- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
