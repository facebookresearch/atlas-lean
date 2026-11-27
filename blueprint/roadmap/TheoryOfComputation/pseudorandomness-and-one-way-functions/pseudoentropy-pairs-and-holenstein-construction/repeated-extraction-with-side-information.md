# Extraction from many independent samples with public side information

Let $n \ge 1$, let $(Z, W)$ be a pair of random variables in which $W$ takes values in $\{0,1\}^{w}$ with $w \ge 1$ and the Shannon conditional entropy satisfies $H(W \mid Z) \ge h$, and let $(Z_1, W_1), \dots, (Z_k, W_k)$ be $k$ independent copies of $(Z, W)$. There is an absolute constant $c$ such that the following holds. Let $\lambda = c\,(w\sqrt{kn} + n)$, let $m = \lfloor kh - \lambda \rfloor$, assumed positive, and let $M$ be a uniformly random $m \times kw$ matrix over $\mathbb{F}_2$, independent of the samples. Then

$$
\bigl(M, Z_1, \dots, Z_k, M\cdot(W_1 \| \cdots \| W_k)\bigr)
$$

is within statistical distance $2^{-n}$ of $(M, Z_1, \dots, Z_k, U_m)$, where $U_m$ is uniform on $\{0,1\}^m$ and independent of the rest.

## Proof sketch

By concentration of the sample conditional entropy of $k$ independent copies, $W_1 \| \cdots \| W_k$ has smooth conditional min-entropy at least $kh - O(w\sqrt{kn})$ given $(Z_1, \dots, Z_k)$, with smoothing parameter $2^{-n-1}$. The family of uniformly random $\mathbb{F}_2$-linear maps is two-universal, so the leftover hash lemma with side information extracts $m$ bits within distance $2^{-n-1}$ of uniform once $m$ is $O(n)$ below that min-entropy.

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Conditional guessing probability and min-entropy](../../../ComputerScience/cryptography/randomness-extraction/conditional-guessing-probability-and-min-entropy.md)
- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
- T. Holenstein and R. Renner, "On the Randomness of Independent Experiments", IEEE Transactions on Information Theory, 2011.
