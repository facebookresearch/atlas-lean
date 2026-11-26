# Game-dependent exponential parallel repetition

For every finite two-player game $G$ as specified, if $\omega^*(G)<1$ then there are real $c,C>0$ such that for every natural number $n$, including zero,

$$\omega^*(G^{\otimes n})\le C e^{-cn}.$$

Constants may depend on $G$. This statement does not separately assume nonempty answer sets.

## Depends on

- [Entangled game value and parallel repetition](entangled-game-value-and-repetition.md)

## Proof depends on

- [Question-distribution-uniform exponential parallel repetition](distribution-uniform-exponential-bound.md)

## Proof outline

For nonempty answer sets absorb the gap and the logarithmic denominator into a positive game-dependent rate. Treat n=0 and empty answer sets with the exact state and value conventions; do not add a nonemptiness hypothesis to the endpoint.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 6](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `standardQuantumParallelRepetition`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/G_QuantumParallelRepetition.lean#L130-L134)
