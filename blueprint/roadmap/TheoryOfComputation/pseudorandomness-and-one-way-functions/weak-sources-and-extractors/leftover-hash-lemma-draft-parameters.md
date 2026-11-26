# Leftover hash lemma with entropy k/δ and collision bound (1+δ)/2^k

Let $n, k, t \ge 0$ and $\delta > 0$. Let $\{h_s : \{0,1\}^n \to \{0,1\}^k\}_{s \in \{0,1\}^t}$ be a family such that, for $s$ uniform, distinct inputs collide with probability at most $(1+\delta)/2^k$. Then for every source $X$ on $\{0,1\}^n$ of min-entropy at least $k/\delta$ and independent uniform $S$, the distribution of $(h_S(X), S)$ (digest followed by seed) is within statistical distance $\sqrt{2\delta}$ of uniform on $\{0,1\}^{k+t}$; equivalently $(s, x) \mapsto h_s(x)$ is a strong extractor with these parameters. The statement holds for all $\delta > 0$, including $k = 0$ and large $\delta$.

## Proof sketch

The collision probability of $(h_S(X), S)$ is at most $2^{-t}\bigl((1+\delta)2^{-k} + 2^{-k/\delta}\bigr)$. The standard bound $\Delta \le \tfrac12\sqrt{2^{k+t}\mathrm{cp} - 1}$ gives at most $\tfrac12\sqrt{\delta + 2^{k - k/\delta}}$, and an elementary estimate shows this is at most $\sqrt{2\delta}$.

## Depends on

- [Seeded randomness extractors](seeded-randomness-extractors.md)
- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Bounded universal hash functions](../../../ComputerScience/cryptography/hash-functions/bounded-universal-hash-functions.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", web draft of January 8, 2007.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-way Function", SIAM Journal on Computing, 1999.
