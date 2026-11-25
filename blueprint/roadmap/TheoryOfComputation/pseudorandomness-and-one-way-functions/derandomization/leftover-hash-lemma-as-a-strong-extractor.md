# Leftover hash lemma as a strong extractor

A function $\mathrm{Ext} : \{0,1\}^n \times \{0,1\}^d \to \{0,1\}^m$ is a *strong $(k, \varepsilon)$-extractor* if for every random variable $X$ on $\{0,1\}^n$ with min-entropy at least $k$ and $U_d$ uniform on $\{0,1\}^d$ and independent of $X$, the distribution of $(U_d, \mathrm{Ext}(X, U_d))$ is within statistical distance $\varepsilon$ of the uniform distribution on $\{0,1\}^{d+m}$.

*Leftover hash lemma.* If $\{h_s : \{0,1\}^n \to \{0,1\}^m\}_{s \in \{0,1\}^d}$ is a pairwise-independent (or even 2-universal) family of hash functions, $\varepsilon > 0$, and $m$ is an integer with $0 \le m \le k - 2\log_2(1/\varepsilon)$, then $\mathrm{Ext}(x, s) = h_s(x)$ is a strong $(k, \varepsilon)$-extractor.

## Depends on

- [Indexed universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal-on.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, Chapter 6, <https://people.seas.harvard.edu/~salil/pseudorandomness/extractors.pdf>: Definition 6.13 (seeded extractors), Definition 6.16 (strong extractors) and Theorem 6.18 (leftover hash lemma).
