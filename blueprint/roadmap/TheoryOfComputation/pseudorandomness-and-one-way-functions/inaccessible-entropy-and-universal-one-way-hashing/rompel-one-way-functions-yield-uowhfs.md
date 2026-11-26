# Rompel: one-way functions yield universal one-way hash functions

If a one-way function exists, then there is a target collision-resistant (universal one-way) keyed hash family with polynomial-time keys and evaluation, defined on bit strings of every polynomial length and compressing them, secure against probabilistic polynomial-time adversaries that commit to a target input before seeing the key. More generally the conclusion holds for every polynomial-time function family with inaccessible average max-entropy (against adversary-dependent accessible sets).

## Proof sketch

Start from the inaccessible-entropy function of the one-way function, amplify the gap by parallel repetition, enumerate a polynomial grid of entropy guesses to obtain one-bit-shrinking candidates that are collision resistant on random inputs, convert to target collision resistance by a target shift, compose candidates with Shoup's masking cascade, and combine the candidates so that one correct guess suffices; Merkle–Damgård-style iteration extends the domain.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Collision resistance and target collision resistance](../../../ComputerScience/cryptography/hash-functions/collision-resistance-and-target-collision-resistance.md)
- [Collision finders and accessible average max-entropy](accessible-average-max-entropy.md)

## Proof depends on

- [Inaccessible average max-entropy from any one-way function](inaccessible-entropy-from-one-way-functions.md)
- [Gap amplification for inaccessible entropy by parallel repetition](inaccessible-entropy-gap-amplification.md)
- [From an inaccessible-entropy gap to a one-bit-shrinking function collision resistant on random inputs](inaccessible-entropy-to-shrinking-collision-resistance.md)
- [Shoup's XOR-masking composition of target collision-resistant compression functions](shoup-xor-masking-composition.md)

## Sources

- J. Rompel, "One-Way Functions are Necessary and Sufficient for Secure Signatures", Proceedings of the 22nd Annual ACM Symposium on Theory of Computing (STOC), 1990.
- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
- V. Shoup, "A Composition Theorem for Universal One-Way Hash Functions", Advances in Cryptology (EUROCRYPT 2000), LNCS 1807, 2000.
