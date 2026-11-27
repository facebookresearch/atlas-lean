# Threshold parallel repetition for finite entangled games

Take arbitrary nonempty finite question sets $X,Y$ and answer sets $A,B$, a probability distribution on $X\times Y$ that need not be a product, and a Boolean acceptance rule for question/answer pairs. A strategy comprises two positive finite Hilbert-space dimensions, a unit vector in their tensor product, and one local POVM per question, with answer probabilities given by the expectation of the tensor product of POVM elements. Write $v$ for the supremum of the win probability over these strategies.

There exists a universal $\kappa_0>0$ such that whenever $v<1$, $0<\delta<1-v$ and $k\ge1$, the following holds. Ask $k$ independent pairs of questions from the same law. Allow arbitrary finite-dimensional strategies of the same tensor-product form, with each local measurement depending on the entire local question vector and returning a whole answer vector. The probability that at least $\lceil(v+\delta)k\rceil$ coordinates win is at most

$$
\exp\!\left(-\frac{\kappa_0\delta^{13}k}{1+\log(|A||B|)}\right).
$$

The same upper bound holds for the supremum over strategies, without requiring any maximizing strategy. All logarithms here are natural.

**Conventions.** Use finite tensor-product strategies with a shared unit vector and positive semidefinite measurement effects summing to identity, the threshold event for the repeated game, and the supremum over finite positive dimensions.

## Depends on

- [Finite entangled games and threshold repetition values](finite-entangled-threshold-value.md)

## Expansion

An extraction or rounding argument converting a high threshold-event probability for a repeated entangled strategy into an improved one-shot strategy, with control at arbitrary correlated question laws. The dimension-independent constants and answer-alphabet dependence are part of that argument.

Build the common strategy and game API, verify normalization for collective POVMs, and separate the threshold conditioning, one-coordinate extraction and quantitative estimate. Pass from each strategy to the supremum without a compactness or attainment assumption over dimensions.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EntangledGames.lean#L64-L75)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/277.md)
- [Accompanying manuscript: Threshold parallel repetition for finite-dimensional entangled games](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Threshold-parallel-repetition-for-finite-dimensional-entangled-games-September-25-2026/paper.pdf)
