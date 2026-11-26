# Internal and external information cost

Fix a distribution $\mu$ on inputs $(X, Y)$ and a (possibly private-coin) protocol $\pi$ with transcript $\Pi$. The *external information cost* is $\mathrm{IC}^{\mathrm{ext}}_\mu(\pi) = I(\Pi; XY)$, what an observer learns about both inputs, and the *internal information cost* is $\mathrm{IC}_\mu(\pi) = I(\Pi; X \mid Y) + I(\Pi; Y \mid X)$, what each player learns about the other's input. The *information complexity* $\mathrm{IC}_\mu(f, \varepsilon)$ is the infimum of the internal cost over protocols computing $f$ with error at most $\varepsilon$ under $\mu$. Both costs are at most the expected transcript length, and $\mathrm{IC} \le \mathrm{IC}^{\mathrm{ext}}$; they coincide under product distributions.

## Depends on

- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Conditional entropy of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Sources

- M. Braverman and A. Rao, "Information Equals Amortized Communication", FOCS 2011.
- A. Rao and A. Yehudayoff, "Communication Complexity and Applications", Cambridge University Press, 2020.
