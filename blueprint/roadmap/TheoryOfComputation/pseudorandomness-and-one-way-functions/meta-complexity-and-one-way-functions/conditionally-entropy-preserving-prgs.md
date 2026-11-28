# Conditionally entropy-preserving pseudorandom generators from one-way functions

Let $\gamma > 0$ be a constant and $\mu : \mathbb{N} \to [0,1]$. An efficiently computable function $G : \{0,1\}^n \to \{0,1\}^{n + \gamma\log n}$ is a *$\mu$-conditionally secure entropy-preserving PRG* ($\mu$-condEP-PRG) if there are nonempty events $E_n \subseteq \{0,1\}^n$ and a constant $\alpha$ (the entropy-loss constant) such that (pseudorandomness) $G(U_n \mid E_n)$, the output on a seed drawn uniformly from $E_n$, is $\mu$-indistinguishable from $U_{n + \gamma\log n}$: for every probabilistic algorithm $D$ running in time polynomial in its input length, $\bigl|\Pr[D(1^n, G(U_n \mid E_n)) = 1] - \Pr[D(1^n, U_{n+\gamma\log n}) = 1]\bigr| < \mu(n)$ for all large $n$; and (entropy preservation) the output keeps almost all the entropy of the seed: $H\bigl(G(U_n \mid E_n)\bigr) \ge n - \alpha\log n$ for all large $n$, with $H$ the Shannon entropy. No lower bound on the probability of $E_n$ is required. If one-way functions exist, then there is a polynomial $t_0$ such that for all constants $\gamma > 1$ and $\delta > 1$ there is a $n^{-\delta}$-condEP-PRG $G_{\delta,\gamma} : \{0,1\}^n \to \{0,1\}^{n+\gamma\log n}$ with running time at most $(\gamma+\delta)\,t_0(n)$ (Liu–Pass, Theorem 5.5). Such generators, in the rate-1 efficient form with $\mu(n) = 1/n^2$ that follows by padding, are used to show that one-way functions make $K^t$ mildly hard on average.

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

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", Proceedings of the 61st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2020; arXiv:2009.11514v1, Definition 2.6 ($\mu$-indistinguishability), Definition 5.1, Theorem 5.2 and Theorems 5.5-5.6.
