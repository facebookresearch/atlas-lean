# Goldreich–Vadhan: every HVSZK problem Karp-reduces to Entropy Difference

For every promise problem $\Pi\in\mathsf{HVSZK}$ there is a polynomial-time Karp reduction $x\mapsto(X_x,Y_x)$ from $\Pi$ to $\mathrm{ED}$: $x\in\Pi_{\mathrm{yes}}$ implies $H(X_x)\ge H(Y_x)+1$ and $x\in\Pi_{\mathrm{no}}$ implies $H(Y_x)\ge H(X_x)+1$.

## Proof sketch

Let $S$ be the honest-verifier simulator, first amplified so that soundness error is tiny and the protocol has $r$ rounds. Let $X_x$ output the simulated transcript (all prover and verifier messages) and let $Y_x$ output the simulated transcript prefixes together with fresh verifier coins, so that the entropy difference measures how much the prover's messages add beyond the verifier's randomness. On YES instances the simulation is statistically close to a real interaction, and the chain rule shows that the verifier's messages contribute their full randomness, giving $H(X_x)\ge H(Y_x)+1$ after repetition; on NO instances, soundness forces the simulated verifier coins to deviate, which shows up as an entropy deficit of at least one bit after amplification.

## Depends on

- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [Shannon entropy](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Sources

- Oded Goldreich and Salil Vadhan, "Comparing Entropies in Statistical Zero Knowledge with Applications to the Structure of SZK", CCC (1999), ECCC TR98-063.
