# Levin–Schnorr theorem and equivalence with Solovay randomness

For an infinite binary sequence $\omega$ the following are equivalent: (1) $\omega$ is Martin-Löf random; (2) there is $c$ such that $K(\omega_1 \cdots \omega_n) \ge n - c$ for all $n$ (prefix complexity); (3) $\omega$ passes every Solovay test.

## Proof sketch

(1)⇒(2): the sets $V_k = \{w : K(w) \le |w| - k\}$ form a Martin-Löf test, since $\sum_w 2^{-K(w)} \le 1$ bounds the measure of $[V_k]$ by $\sum_{w \in V_k} 2^{-|w|} \le 2^{-k}$; a random $\omega$ escapes some $[V_c]$, which is (2). (2)⇒(1): take a universal test $(U_k)$ with each $U_k$ given as a prefix-free c.e. set; requesting a codeword of length $|w| - k$ for every $w \in U_{2k}$ has total weight at most $\sum_k 2^{k} 2^{-2k} \le 1$, so by Kraft–Chaitin $K(w) \le |w| - k + O(1)$ on $U_{2k}$, and a sequence in $\bigcap_k [U_k]$ violates (2). A Martin-Löf test (in prefix-free form) is a Solovay test, and from a Solovay test with $\sum_i 2^{-|w_i|} \le 1$ (drop finitely many strings) the sets of sequences extending at least $2^k$ of its strings form a Martin-Löf test that captures every sequence extending infinitely many $w_i$.

## Depends on

- [Martin-Löf tests and Martin-Löf randomness](martin-lof-tests-and-randomness.md)
- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)

## Proof depends on

- [The online Kraft–Chaitin theorem](online-kraft-chaitin-theorem.md)

## Sources

- C.-P. Schnorr, "Process Complexity and Effective Random Tests", Journal of Computer and System Sciences 7(4), 376–388, 1973.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
