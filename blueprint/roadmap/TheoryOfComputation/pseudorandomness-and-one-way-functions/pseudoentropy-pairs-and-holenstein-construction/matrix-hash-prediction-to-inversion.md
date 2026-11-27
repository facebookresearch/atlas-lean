# Prediction from a leaked matrix hash yields inversion

Let $f : \{0,1\}^n \to \{0,1\}^{m(n)}$ and $\varphi : \mathbb{N} \to [0,1]$ be computable in time polynomial in $n$, and let $(X, B)$ be the hashed parity pair of $f$, with observation $X = (f(x), i, M, (Mx)_{1..i}, r)$ and hidden bit $B = \langle x, r\rangle$. There is an oracle algorithm $A$, independent of fiber sizes, such that for every predictor $P$ whose correlation with the hidden bit satisfies

$$\mathbb{E}\bigl[(-1)^{P(X) \oplus B}\bigr] \ge 1 - H(B \mid X) - \varphi(n),$$

$A^P$ inverts $f$ on $f(x)$, for uniform $x$, with probability $\Omega(n^{-3})\,2^{-n\varphi(n)}$, using $O(n^3)$ calls to $P$. On input $y$ the inverter draws the hash length and the matrix as the pair does and the leaked prefix uniformly, runs Goldreich–Levin decoding with $P$ as oracle, and checks each candidate against $y$. This is Holenstein's Lemma 4, proved there for the hash $x \mapsto (ax)_{1..i}$ with $a \in \mathrm{GF}(2^n)$ and $i$ uniform in $[n]$; the proof uses only that the hash family is universal and that $i$ is almost uniform on a range of size $\Theta(n)$, which holds for a uniform $n \times n$ matrix and the hash length of the pair.

## Proof sketch

Restrict to hash lengths $i \le \log_2|f^{-1}(f(x))| + n\varphi + 3$, which carry enough of the predictor's correlation that its expected advantage on a fixed preimage stays $\Omega(1/n)$. Split the leaked prefix into a part of length about $\log_2|f^{-1}(f(x))| - 2\log_2(4n)$, which is $1/(4n)$-close to uniform given $f(x)$ and $M$ by the leftover hash lemma, and a suffix of at most $2\log_2(4n) + n\varphi + 3$ bits, which the inverter guesses with probability $\Omega(n^{-2})\,2^{-n\varphi}$. With probability $\Omega(1/n)$ the predictor then has advantage above $1/(4n)$ on the inner product with a preimage, and Goldreich–Levin recovers one.

## Depends on

- [Hashed parity pair of a function](hashed-parity-pair.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Goldreich–Levin list decoding of the Hadamard code with oracle access](../hard-core-predicates-and-stretch/goldreich-levin-list-decoding.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006, Lemma 3, Lemma 4 and its proof (Games 0-5).
