# Conditionally entropy-preserving pseudorandom generators from one-way functions

A $\mu$-*conditionally entropy-preserving PRG* is a polynomial-time $G : \{0,1\}^n \to \{0,1\}^{n + \gamma\log n}$ together with an event $E_n$ of probability at least $1 - \mu(n)$ over the seed such that $G(U_n)$ conditioned on $E_n$ is computationally indistinguishable from uniform and the seed retains almost all of its entropy: $H(U_n \mid E_n) \ge n - c\log n$ for a constant $c$. If one-way functions exist, then for every constant $\gamma$ there is a $\mu$-conditionally entropy-preserving PRG with $\mu$ an inverse polynomial. Such generators are used to show that one-way functions make $K^t$ mildly hard on average.

## Proof sketch

Build the generator from the inaccessible-information structure of the one-way function: hash the input with a random-length universal hash so that, conditioned on the good event that the length matches the fiber size, the output has extractable pseudoentropy; Goldreich–Levin bits supply the $\gamma\log n$ extra output bits.

## Depends on

- [Asymptotic PRG security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/prgsecure.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

- [Goldreich–Levin for arbitrary one-way functions](../hard-core-predicates-and-stretch/goldreich-levin-for-arbitrary-one-way-functions.md)
- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", Proceedings of the 61st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2020.
