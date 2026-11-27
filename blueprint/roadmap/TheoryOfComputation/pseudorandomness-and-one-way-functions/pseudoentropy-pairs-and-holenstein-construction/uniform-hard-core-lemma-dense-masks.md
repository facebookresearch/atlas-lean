# Uniform hard-core lemma: dense masks fooling efficient sequence tests

Let $(X, B)$ be a samplable pair with pseudoentropy gap $\gamma$ against probabilistic polynomial-time predictors. Then for every efficient test $T$ on sequences of $k$ independent samples (with $k$ polynomial) and every density $\delta$ below the entropy threshold $H(B\mid X)$, there is, for all large $n$, a soft mask $\mu$ of density at least $\delta$, with nonzero mask probabilities at least $1/p(n)$ for a polynomial $p$, such that $T$ distinguishes $k$ samples $(X_j, B_j)$ from $k$ samples $(X_j, B'_j)$ with the labels freshly masked by $\mu$ with advantage at most $\gamma/4$. One threshold works uniformly for all tests in an efficiently indexed polynomial-size family.

## Proof sketch

Otherwise run a boosting loop: maintain multiplicative soft weights, at each round learn from the test a predictor with good weighted correlation via a random-coordinate hybrid, and combine predictors by a clipped majority vote. A potential argument shows the loop terminates in polynomially many rounds with a predictor violating the pseudoentropy gap.

## Depends on

- [Samplable pseudoentropy pair with a prediction gap](samplable-pseudoentropy-pair.md)
- [Fresh masking lower-bounds the conditional entropy of a label](fresh-masking-lower-bounds-label-entropy.md)

## Proof depends on

- [Next-bit predictors and distinguishers: exact transfer and the positional sum bound](../../../ComputerScience/cryptography/security-games/computational-indistinguishability-of-ensembles/predictor-distinguisher-correspondence.md)
- [Selecting the best candidate by repeated trials](../../../ComputerScience/cryptography/security-games/probabilistic-oracle-programs/selecting-the-best-candidate-by-trials.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- T. Holenstein, "Key Agreement from Weak Bit Agreement", Proceedings of the 37th Annual ACM Symposium on Theory of Computing (STOC), 2005.
- R. Impagliazzo, "Hard-Core Distributions for Somewhat Hard Problems", Proceedings of the 36th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1995.
