# Entangled game value and parallel repetition

A game has finite question sets $X,Y$, finite answer sets $A,B$, a nonnegative joint distribution $\mu$ on $X\times Y$ of total mass one, and a Boolean winning predicate $W(x,y,a,b)$. A strategy chooses arbitrary finite local Hilbert dimensions, a positive semidefinite trace-one state $\rho$ on the tensor product, and for each question the corresponding player's positive semidefinite answer effects $(P^x_a)_a$ and $(Q^y_b)_b$ summing to identity. The conditional probability for an outcome is $\operatorname{Re}\,\mathrm{tr}(\rho(P^x_a\otimes Q^y_b))$.

Write $\omega^*(G)$ for the supremum in $\mathbb R$ of the $\mu$-weighted total of winning outcome probabilities over these strategies. In $G^{\otimes n}$, the questions of the $n$ rounds are sampled independently with distribution $\mu$; each player receives and answers a length-$n$ tuple, and winning requires every coordinate to win. The supremum for repetition permits a joint strategy, not just independent strategies. The real supremum is totalized to zero for the empty set of strategies.

## Expansion

Verify normalization, validity of the Born rule and that the value is bounded by one. For nonempty answer sets exhibit at least one finite strategy; keep the empty-answer and zero-repeat conventions separate.

## Sources

- [Pinned probability and repetition model](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/G_QuantumParallelRepetition.lean#L12-L100)
