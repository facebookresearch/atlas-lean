# Pseudorandom generators from samplable pseudoentropy pairs

Let $(X, B)$ be an exactly samplable pair with an inverse-polynomial pseudoentropy gap. Then there is a pseudorandom generator with one bit of stretch (and hence, by stretch amplification, with any polynomial stretch). The generator samples many independent copies of the pair from one seed, and for every candidate in a polynomial-size grid of guesses for $H(X)$ and $H(B \mid X)$ it hashes the observations, the labels and the remaining sampler randomness with three independent public matrices; it outputs the XOR of the padded candidate outputs. No entropy estimate needs to be known in advance.

## Proof sketch

For the correct grid point, the three extractions are replaced by uniform strings one at a time: the remaining-seed and observation steps are statistical (repeated extraction), and the label step is computational, using the uniform hard-core lemma to replace labels by masked labels with extra entropy. Every candidate expands, and XOR with independent pseudorandom candidates preserves pseudorandomness of the correct one.

## Depends on

- [Samplable pseudoentropy pair with a prediction gap](samplable-pseudoentropy-pair.md)
- [Asymptotic PRG security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/prgsecure.md)

## Proof depends on

- [Uniform hard-core lemma: dense masks fooling efficient sequence tests](uniform-hard-core-lemma-dense-masks.md)
- [Extraction from many independent samples with public side information](repeated-extraction-with-side-information.md)
- [XOR of independently seeded generators is pseudorandom if one is](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generator-attacks-and-transformations/xor-of-independently-seeded-generators.md)
- [Stretch amplification of a one-bit pseudorandom generator](../hard-core-predicates-and-stretch/prg-stretch-amplification.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
