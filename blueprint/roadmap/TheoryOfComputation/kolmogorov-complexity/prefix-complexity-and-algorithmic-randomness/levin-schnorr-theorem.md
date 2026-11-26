# Levin–Schnorr theorem and equivalence with Solovay randomness

For an infinite binary sequence $\omega$ the following are equivalent: (1) $\omega$ is Martin-Löf random; (2) there is $c$ such that $K(\omega_1 \cdots \omega_n) \ge n - c$ for all $n$ (prefix complexity); (3) $\omega$ passes every Solovay test.

## Proof sketch

(1)⇒(2): the sets $V_k = \{w : K(w) \le |w| - k\}$ form a test, since $\sum_w 2^{-K(w)} \le 1$ bounds their measure by $2^{-k}$, and conversely a universal test can be compressed via Kraft–Chaitin: strings in $V_{2k}$ receive codewords of length $|w| - k$, so (2)⇒(1). A Martin-Löf test is a Solovay test, and from a Solovay test one builds a Martin-Löf test of sequences extending at least $2^k$ of its strings.

## Depends on

- [Martin-Löf tests and Martin-Löf randomness](martin-lof-tests-and-randomness.md)
- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)

## Proof depends on

- [The online Kraft–Chaitin theorem](online-kraft-chaitin-theorem.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
