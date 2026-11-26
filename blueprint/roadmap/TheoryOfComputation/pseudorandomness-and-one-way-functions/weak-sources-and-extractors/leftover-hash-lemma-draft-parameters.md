# Leftover hash lemma with entropy k/δ and collision bound (1+δ)/2^k

Let $n, k, t \ge 0$ and $\delta > 0$. Let $\{h_s : \{0,1\}^n \to \{0,1\}^k\}_{s \in \{0,1\}^t}$ be a family such that, for $s$ uniform, distinct inputs collide with probability at most $(1+\delta)/2^k$. Then for every source $X$ on $\{0,1\}^n$ of min-entropy at least $k/\delta$ and independent uniform $S$, the distribution of $(h_S(X), S)$ (digest followed by seed) is within statistical distance $\sqrt{2\delta}$ of uniform on $\{0,1\}^{k+t}$; equivalently $(s, x) \mapsto h_s(x)$ is a strong extractor with these parameters. The statement holds for all $\delta > 0$, including $k = 0$ and large $\delta$.

## Proof sketch

If $k = 0$ the digest is constant, $(h_S(X), S)$ is uniform and the distance is $0$; if $\delta \ge 1/2$ then $\sqrt{2\delta} \ge 1$ bounds every statistical distance. Otherwise $k \ge 1$ and $\delta < 1/2$. The collision probability of $(h_S(X), S)$ is at most $2^{-t}\bigl((1+\delta)2^{-k} + 2^{-k/\delta}\bigr)$, and the standard bound $\Delta \le \tfrac12\sqrt{2^{k+t}\mathrm{cp} - 1}$ gives at most $\tfrac12\sqrt{\delta + 2^{k(1 - 1/\delta)}}$. Since $1 - 1/\delta < 0$, $2^{k(1-1/\delta)} \le 2^{1 - 1/\delta} \le \delta$ (the ratio $2^{1-1/\delta}/\delta$ increases on $(0, 1/2]$ and equals $1$ at $1/2$), so the distance is at most $\tfrac12\sqrt{2\delta} \le \sqrt{2\delta}$.

## Depends on

- [Seeded randomness extractors](seeded-randomness-extractors.md)
- [Bounded universal hash functions](../../../ComputerScience/cryptography/hash-functions/bounded-universal-hash-functions.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", web draft of January 8, 2007.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-way Function", SIAM Journal on Computing, 1999.
