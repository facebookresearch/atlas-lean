# Extraction from many independent samples with public side information

Let $(Z_j, W_j)_{j=1}^{k}$ be $k$ independent samples of a pair in which $W_j$ takes values in $\{0,1\}^{w}$ and $H(W_j \mid Z_j) \ge h$, and let the sampler's information be bounded by $I$ bits per sample. Let $M$ be a uniform Boolean matrix with $k h - \lambda$ rows, where $\lambda = \Theta(I\sqrt{k \cdot n})$ accounts for concentration and the leftover hash loss. Then

$$\bigl(M, (Z_j)_{j}, M\cdot(W_1 \| \cdots \| W_k)\bigr)$$

is within statistical distance $2^{-\Omega(n)}$ of $(M, (Z_j)_j, U)$ with $U$ uniform, provided $k \ge c\, n I^2 / \varepsilon^2$ for the required slack $\varepsilon$.

## Proof sketch

By concentration of the sample entropy of $k$ independent samples, the concatenated labels have conditional smooth min-entropy at least $kh - \lambda/2$ given the observations except with exponentially small probability; the leftover hash lemma for the matrix family then extracts $kh - \lambda$ almost uniform bits.

## Depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Conditional guessing probability and min-entropy](../../../ComputerScience/cryptography/randomness-extraction/conditional-guessing-probability-and-min-entropy.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
