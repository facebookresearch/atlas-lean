# Explicit linear strong extractors: Toeplitz hashing and Trevisan–RRV

(Toeplitz.) Multiplying $x \in \{0,1\}^n$ by a uniform $m \times n$ Boolean Toeplitz matrix (no offset) is a $2^{-m}$-universal linear family, hence a linear strong $(k, \delta/2)$-extractor with seed length $m + n - 1$ whenever $m + 2\log_2(1/\delta) \le k$.

(Trevisan–RRV.) A *weak design* with parameter $\rho$ is a family of $t$-subsets $S_1, \dots, S_m$ of a universe of size $u$ with $\sum_{j < i} 2^{|S_i \cap S_j|} \le \rho(i-1)$ for all $i$; the Raz–Reingold–Vadhan method of conditional expectations constructs one deterministically with $\rho = 2$ and $u = 2t^2$. Evaluating an $\mathbb{F}_2$-linear binary code with good list-decoding (a Reed–Solomon code over $\mathbb{F}_{2^w}$ concatenated with the Hadamard code, whose list size at agreement $1/2 + \delta$ is below $1/(2\delta^2)$ by the binary Johnson bound) at the positions indexed by the design blocks of the seed gives an explicit linear strong $(k, \varepsilon)$-extractor with seed length $8w^2 = O(\log^2(nm/\varepsilon))$ and output length $m$ whenever $2m + 3\log_2(m/\varepsilon) + 2 \le k$.

## Proof sketch

Toeplitz: $Td$ is uniform for $d \ne 0$, so the leftover hash lemma applies. Trevisan: if the output were distinguishable, the hybrid argument plus the weak design property yields a short advice string predicting a bit of the codeword of $x$ with advantage $\varepsilon/m$; list decoding then confines $x$ to a small set, contradicting min-entropy $k$. Linearity is inherited from the linear code.

## Depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)
- [Toeplitz hashing is pairwise independent](../../../../ComputerScience/data-structures/hashing/limited-independence-hash-families/toeplitz-hashing.md)
- [Leftover hash lemma](../../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Combinatorial designs for the Nisan–Wigderson generator](../../derandomization/combinatorial-designs-for-the-nisanwigderson.md)
- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Local decoding of the Hadamard code](../../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)
- [Johnson bound](../../../../InformationTheory/error-correcting-codes/list-decoding/johnson-bound.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
- N. Nisan and A. Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences, 1994.
- V. Guruswami, A. Rudra and M. Sudan, "Essential Coding Theory", draft book, 2019.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
