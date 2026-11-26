# Boolean pseudorandom functions require circuits of size at least 2n − 2

Let $(F_n)$ be a family of distributions over Boolean functions $\{0,1\}^n \to \{0,1\}$ that is indistinguishable from a uniformly random function by probabilistic polynomial-time oracle adversaries (sampling and evaluation need not be efficient). Then for all sufficiently large $n$, the support of $F_n$ contains a function whose minimum circuit size over the full binary basis $B_2$ (every fan-in-two gate costs one, including constants; wiring is free) is at least $2n - 2$.

## Proof sketch

Functions of $B_2$-complexity below $2n-2$ have a structural weakness (gate elimination shows some input variable, or pair of variables, enters the function in a degenerate way), which an efficient adversary detects with constant advantage by querying the function on a few correlated inputs; a random function exhibits such degeneracy only with negligible probability.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)
- [Evaluation of a flat Boolean circuit](../../complexity-classes/time-and-space-complexity-classes/circuit-eval.md)

## Sources

- Z. Fan, J. Li and T. Yang, "The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity", Proceedings of the 54th Annual ACM Symposium on Theory of Computing (STOC), 2022.
