# Explicit linear strong extractors: Toeplitz hashing and Trevisan–RRV

(Toeplitz.) Multiplying $x \in \{0,1\}^n$ by a uniform $m \times n$ Boolean Toeplitz matrix (no offset) is a $2^{-m}$-universal linear family, hence a linear strong $(k, \delta/2)$-extractor with seed length $m + n - 1$ whenever $m + 2\log_2(1/\delta) \le k$.

(Trevisan–RRV.) For every $n, k, m \in \mathbb{N}$ and $\varepsilon > 0$ with $m \le k \le n$ there is an explicit linear strong seeded extractor $\mathrm{LSExt} : \{0,1\}^n \times \{0,1\}^d \to \{0,1\}^m$ for min-entropy $k$ and error $\varepsilon$ with seed length $d = O\bigl(\log^2(n/\varepsilon)/\log(k/m)\bigr)$.

## Proof sketch

Toeplitz: $Td$ is uniform for $d \ne 0$, so the leftover hash lemma applies. Trevisan: evaluate an $\mathbb{F}_2$-linear binary code with good list decoding at the positions indexed by the blocks of a weak design applied to the seed. If the output were distinguishable, the hybrid argument plus the weak design property yields a short advice string predicting a bit of the codeword of $x$ with advantage $\varepsilon/m$; list decoding then confines $x$ to a small set, contradicting min-entropy $k$. Linearity is inherited from the linear code.

Derived instantiation (explicit constants not stated in the cited sources): a *weak design* with parameter $\rho$ is a family of $t$-subsets $S_1, \dots, S_m$ of a universe of size $u$ with $\sum_{j < i} 2^{|S_i \cap S_j|} \le \rho(i-1)$ for all $i$, and the Raz–Reingold–Vadhan method of conditional expectations constructs one deterministically with $\rho = 2$ and $u = \lceil t/\ln\rho\rceil t \le 2t^2$. Using a Reed–Solomon code over $\mathbb{F}_{2^w}$ concatenated with the Hadamard code (list size below $1/(2\delta^2)$ at agreement $1/2 + \delta$, by the binary Johnson bound) as the linear code, with $t = 2w$ seed bits per design block, gives a seed of $u \le 2t^2 = 8w^2 = O(\log^2(nm/\varepsilon))$ bits and output length $m$, for min-entropy $k$ exceeding $2m$ by the lower-order terms of the Raz–Reingold–Vadhan analysis.

## Depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)
- [Toeplitz hashing is pairwise independent](../../../../ComputerScience/data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/toeplitz-hashing.md)
- [Leftover hash lemma](../../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Proof depends on

- [Combinatorial designs for the Nisan–Wigderson generator](../../derandomization/combinatorial-designs-for-the-nisanwigderson.md)
- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Local decoding of the Hadamard code](../../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)
- [Johnson bound](../../../../InformationTheory/error-correcting-codes/list-decoding/johnson-bound.md)

## Sources

- E. Chattopadhyay, V. Goyal and X. Li, "Non-Malleable Extractors and Codes, with their Many Tampered Extensions", Proceedings of the 48th ACM Symposium on Theory of Computing (STOC 2016), 285–298, 2016, numbering of arXiv:1505.00107v1, Definition 3.5 (linear seeded extractor) and Theorem 3.14 ([Tre01][RRV02]: explicit linear strong seeded extractor).
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012, Problem 3.3 (Toeplitz matrices) and Theorem 6.18 (leftover hash lemma).
- N. Nisan and A. Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences 49(2), 149–167, 1994.
- L. Trevisan, "Extractors and Pseudorandom Generators", Journal of the ACM 48(4), 860–879, 2001.
- R. Raz, O. Reingold and S. Vadhan, "Extracting All the Randomness and Reducing the Error in Trevisan's Extractors", Journal of Computer and System Sciences 65(1), 97–128, 2002 (weak designs).
- V. Guruswami, "List Decoding of Error-Correcting Codes", Lecture Notes in Computer Science 3282, Springer, 2004 (binary Johnson bound).
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
