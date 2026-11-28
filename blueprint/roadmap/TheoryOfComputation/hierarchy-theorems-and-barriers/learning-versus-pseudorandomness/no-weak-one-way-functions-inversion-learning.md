# Without weak one-way functions, inverting the labelling map gives accurate keys on infinitely many scales

Let a key-and-point family be given by a polynomial-time predicate $F_n(K, x)$ with key length $\kappa(n)$ and a polynomial number $m(n)$ of samples, and let $L_n$ map a key and $m(n)$ points of $n$ bits to the points followed by their labels. If no weak one-way function exists, then for every positive polynomial $p$ there is a uniform probabilistic polynomial-time inverter for $L$ that succeeds with probability greater than $1 - 1/p(n)$ on infinitely many $n$; at those scales the key read off its answer on a uniform labelled sample is consistent with the sample, hence has small uniform error by the inversion bound. This is a step towards, not the statement of, the equivalence between average-case learning and one-way functions; only the inverter's efficiency is certified, not that of the induced learner as a map on samples.

## Proof sketch

The labelling map is polynomial-time computable on suitably encoded inputs, so if it were weakly one-way a weak one-way function would exist. Its failure to be weakly one-way gives, for each polynomial $p$, an inverter succeeding with probability above $1 - 1/p$ on infinitely many lengths. A uniform input is a uniform key with uniform examples, so the inversion bound applies at those lengths.

## Depends on

- [Weak one-way function](../../pseudorandomness-and-one-way-functions/one-way-function-transformations/weak-one-way-function.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Learning by inverting the labelling map of a keyed family (Occam form)](learning-by-inverting-the-labelling-map.md)

## Sources

- Avrim Blum, Merrick Furst, Michael Kearns and Richard J. Lipton, "Cryptographic Primitives Based on Hard Learning Problems", Advances in Cryptology (CRYPTO 1993), 1993.
- Russell Impagliazzo and Leonid A. Levin, "No Better Ways to Generate Hard NP Instances than Picking Uniformly at Random", Proceedings of the 31st Annual Symposium on Foundations of Computer Science, 1990.
