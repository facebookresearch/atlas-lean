# From an inaccessible-entropy gap to a one-bit-shrinking function collision resistant on random inputs

Let $F_1 : \{0,1\}^{n_1} \to \{0,1\}^{m_1}$ have real sample entropy above $K_{\min}$ and accessible sets of log-size below $A_{\max}$, each except on small bad sets. For $A_{\max} + \omega(\log n) \le j \le K_{\min} - \omega(\log n)$, composing $F_1$ with a pairwise-independent input hash that reduces the entropy to about $j$ bits, followed by a two-universal output hash, yields a function $F_3^{(j)} : \{0,1\}^{N_3} \to \{0,1\}^{N_3 - 1}$ that shrinks by exactly one bit and for which every efficient algorithm, given a uniform input $x$, finds $x' \ne x$ with $F_3^{(j)}(x') = F_3^{(j)}(x)$ only with negligible probability.

## Proof sketch

The input hash makes fibers of $F_2^{(j)}$ almost singletons inside the accessible set while keeping enough real entropy for compression; a collision outside the accessible set contradicts the accessible-entropy bound. The output hash is chosen to shrink by one bit while preserving these properties up to negligible error.

## Depends on

- [Collision finders and accessible average max-entropy](accessible-average-max-entropy.md)
- [Universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
