# Question-distribution-uniform exponential parallel repetition

There is an absolute real $c>0$ such that for every finite two-player game with nonempty answer sets $A,B$, arbitrary joint question distribution, and gap $\epsilon=1-\omega^*(G)>0$, and every positive integer $n$,

$$\omega^*(G^{\otimes n})\le \exp\!\left(-c\frac{\epsilon^{13}}{\epsilon+\log(|A||B|)}\,n\right).$$

The logarithm is natural. The constant $c$ is chosen before the game; in particular no product or uniformity assumption is made on the question distribution.

## Depends on

- [Entangled game value and parallel repetition](entangled-game-value-and-repetition.md)

## Expansion

Develop the information and operator estimates for arbitrary joint question laws, prove the one-step conditioning argument, and audit the uniform constant, gap exponent and answer-size term without assuming product questions within a round.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 6](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `distributionUniformExponential`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/G_QuantumParallelRepetition.lean#L112-L127)
