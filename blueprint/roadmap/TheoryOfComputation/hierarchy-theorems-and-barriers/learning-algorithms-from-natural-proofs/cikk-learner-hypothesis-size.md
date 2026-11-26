# The CIKK learner's hypotheses are circuits of size $2^{O(g + e + \ell)}$ times the test size

In the learner from a dense test, on every target and every seed, the output hypothesis has De Morgan circuit complexity at most

$$
2^{11g + 9e + 3\ell + 80}\,(c + 1),
$$

where $c$ is the De Morgan circuit complexity of the test $D$. The exact bound is affine in $c$, with $T(F+1)(2^K - 1)$ copies of the test, where $T$, $F$, $K$ are the numbers of decoder trials, fixed positions and Goldreich-Levin masks.

## Proof sketch

The output equals one run's hypothesis, which is the direct-product decoder applied to Goldreich-Levin candidates built on the Nisan-Wigderson hypothesis of the negated test. Compose the three size bounds: the reconstruction adds a multiplexer per output bit to one copy of the test, each Goldreich-Levin output bit uses $2^K - 1$ copies, and the decoder uses $T(F+1)$ copies of that.

## Depends on

- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)

## Proof depends on

- [Nisan-Wigderson reconstruction as a membership-query weak learner (one run)](nisan-wigderson-reconstruction-weak-learner.md)
- [Best-of-k selection boosts the confidence of a membership-query learner](../../circuit-complexity/learning-under-the-uniform-distribution/best-of-k-confidence-boosting.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
