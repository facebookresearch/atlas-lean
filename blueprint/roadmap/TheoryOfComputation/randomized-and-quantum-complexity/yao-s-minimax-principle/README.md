# Yao's minimax principle

For a problem with finitely many inputs and finitely many deterministic algorithms, a randomized
algorithm is a probability distribution on the algorithms. Yao's minimax principle (A. C. Yao,
FOCS 1977) says that the best worst-case expected cost of a randomized algorithm equals the
best expected cost of a deterministic algorithm against the hardest input distribution. The
inequality used in practice is elementary: to lower-bound randomized algorithms one exhibits an
input distribution on which every deterministic algorithm is expensive. The equality is von
Neumann's minimax theorem for the matrix game between the input player and the algorithm
player. The presentation follows S. Arora and B. Barak, *Computational Complexity: A Modern
Approach* (web draft of 2007-01-08), Section 11.6.

- [Yao's principle, lower-bound form](exists-le-expected-cost.md)
- [Yao's minimax principle](yao-minimax.md)

## Yao's principle by averaging

- [Yao's principle by averaging, algorithm side](yao-exists-det.md)
- [Yao's principle by averaging, input side](yao-exists-input.md)

## Related topics

- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/README.md): the theorem about matrix games that the principle specializes.
- [Randomized communication protocols](../../communication-complexity/randomized-communication-protocols/README.md): the communication version (Rao and Yehudayoff, Theorem 3.3), equating randomized and distributional communication complexity, is proved there.
- [Bounded-error probabilistic classes RP and BPP](../bounded-error-probabilistic-classes-rp-and-bpp/README.md): randomized algorithms in the Turing-machine setting.
