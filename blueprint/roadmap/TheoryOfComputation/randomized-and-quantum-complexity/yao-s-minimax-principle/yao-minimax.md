# Yao's minimax principle

Let $m, n \ge 1$ and let $C$ be a real $m \times n$ matrix, $C(a, x)$ being the cost of the $a$-th of
$m$ deterministic algorithms on the $x$-th of $n$ inputs. The randomized complexity equals the
distributional complexity:

$$
\min_{R} \max_{x} \sum_{a} R(a)\, C(a, x) = \max_{D} \min_{a} \sum_{x} C(a, x)\, D(x),
$$

where $R$ ranges over the probability distributions on the algorithms and $D$ over the probability
distributions on the inputs (the extrema over distributions are infima and suprema). The proof is von Neumann's minimax theorem for the matrix game in which the input player
maximizes and the algorithm player minimizes.

## Informally uses

- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md): Arora and Barak derive Yao's lemma from it, for the game in which one player picks an input and the other an algorithm.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08,
  Section 11.6, equations (10) and (11).
- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 3.3 (the communication
  version).
