# Pseudorandom generators from samplable pseudoentropy pairs

Let $(X, B)$ be an exactly samplable pair with an inverse-polynomial pseudoentropy gap. Then there is a pseudorandom generator with one bit of stretch (and hence, by stretch amplification, with any polynomial stretch). The generator follows Holenstein's proof of Theorem 1. For each of the $N$ candidates $(\alpha, \beta)$ of a polynomial-size grid of guesses for $H(B \mid X)$ and $H(X)$, a candidate function $h_{\alpha,\beta} : \{0,1\}^\ell \to \{0,1\}^{\ell+1}$ samples $k$ independent copies of the pair from its input and hashes the observations, the labels and the remaining sampler randomness to lengths set by $(\alpha, \beta)$, with three independent seeded universal hash functions whose seeds are part of the input and are copied to the output; every candidate expands for all large $n$, and $h_{\alpha,\beta}$ keeps one bit of the stretch. Iterating $h_{\alpha,\beta}$ as in stretch amplification gives $h'_{\alpha,\beta} : \{0,1\}^\ell \to \{0,1\}^{N\ell+1}$. The generator splits its seed of length $N\ell$ into $N$ blocks of length $\ell$, applies each $h'_{\alpha,\beta}$ to its own block, and outputs the XOR of the $N$ outputs, so it maps $N\ell$ bits to $N\ell + 1$ bits. No entropy estimate needs to be known in advance.

## Proof sketch

For the correct grid point, the three extractions are replaced by uniform strings one at a time: the remaining-seed and observation steps are statistical (repeated extraction), and the label step is computational, using the uniform hard-core lemma to replace labels by masked labels with extra entropy. Iteration preserves pseudorandomness of the correct candidate by the hybrid argument, and since the other candidates run on independent seed blocks, XOR with their outputs preserves it too.

## Depends on

- [Samplable pseudoentropy pair with a prediction gap](samplable-pseudoentropy-pair.md)
- [Asymptotic PRG security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/prgsecure.md)

## Proof depends on

- [Uniform hard-core lemma: dense masks fooling efficient sequence tests](uniform-hard-core-lemma-dense-masks.md)
- [Extraction from many independent samples with public side information](repeated-extraction-with-side-information.md)
- [XOR of independently seeded generators is pseudorandom if one is](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generator-attacks-and-transformations/xor-of-independently-seeded-generators.md)
- [Stretch amplification of a one-bit pseudorandom generator](../hard-core-predicates-and-stretch/prg-stretch-amplification.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006, Lemma 5 and the proof of Theorem 1.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
