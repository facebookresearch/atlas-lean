# Internal and external information cost

Fix a distribution $\mu$ on inputs $(X, Y)$ and a protocol $\pi$ with public random string $R$, independent of $(X, Y)$ (constant for a private-coin protocol), and message sequence $M$; messages are prefix-free strings as in Braverman–Rao. The *transcript* is $\Pi = (R, M)$: it includes the public randomness. The *external information cost* is $\mathrm{IC}^{\mathrm{ext}}_\mu(\pi) = I(\Pi; XY) = I(M; XY \mid R)$, what an observer learns about both inputs, and the *internal information cost* is $\mathrm{IC}_\mu(\pi) = I(\Pi; X \mid Y) + I(\Pi; Y \mid X) = I(M; X \mid YR) + I(M; Y \mid XR)$, what each player learns about the other's input. The *information complexity* $\mathrm{IC}_\mu(f, \varepsilon)$ is the infimum of the internal cost over protocols computing $f$ with error at most $\varepsilon$ under $\mu$. Both costs are at most the expected number of message bits $\mathbb{E}|M|$; only message bits count, never public random bits. Moreover $\mathrm{IC} \le \mathrm{IC}^{\mathrm{ext}}$, with equality under product distributions.

Leaving $R$ out of $\Pi$ without conditioning on it would break these statements: with independent fair bits $X, Y, R$ and messages $M = (X \oplus R, Y \oplus R)$, $I(M; XY) = 1$ but $I(M; X \mid Y) + I(M; Y \mid X) = 2$, although the inputs are independent.

## Depends on

- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Conditional entropy of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Sources

- M. Braverman and A. Rao, "Information Equals Amortized Communication", FOCS 2011; ECCC report TR10-083 (Section 2: the transcript concatenates the public randomness with the messages, and Lemma 2.14: the internal cost is the average over $R$).
- A. Rao and A. Yehudayoff, "Communication Complexity and Applications", Cambridge University Press, 2020.
