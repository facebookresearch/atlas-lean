# Fourier extraction from sumsets and the bent inner-product sumset extractor

For independent distributions $A, B$ on $\{0,1\}^n$, $\mathrm{bias}_{A+B}(S) = \mathrm{bias}_A(S)\,\mathrm{bias}_B(S)$ for every $S$. Consequently, if $f : \{0,1\}^n \to \{0,1\}$ has all Fourier coefficients of $(-1)^f$ bounded by $\beta$ in absolute value, then for sources of min-entropies $k_1, k_2$ the bit $f(A+B)$ is within $\tfrac12\beta\,2^{n - (k_1+k_2)/2}$ of uniform. The inner-product bent function on $n = 2r$ bits, $f(u, v) = \langle u, v\rangle$, therefore is a $(k_1, k_2, \tfrac12 2^{(n - k_1 - k_2)/2})$ sumset extractor (with a linear last bit for odd $n$, threshold $k_1 + k_2 > n + (n \bmod 2)$), and on even length the threshold is exact: it fails at $k_1 = k_2 = r$. Sumset extractors are invariant under translation and linear automorphisms, and may be checked on flat sources.

## Proof sketch

Characters are multiplicative under XOR and $A, B$ are independent. Expand the bias of $f(A+B)$ in the Fourier basis, bound each coefficient by $\beta$, and apply Cauchy–Schwarz and Parseval to $\sum_S|\mathrm{bias}_A(S)\mathrm{bias}_B(S)|$ as in Chor–Goldreich. A bent function has $\beta = 2^{-n/2}$. For exactness, take $A$ and $B$ both uniform on $\{(u,0)\}$ (each of min-entropy $r$), so $A+B$ lies in $\{(w,0)\}$, where the inner product is $0$.

## Depends on

- [Affine sources, affine extractors and sumset extractors](affine-sources-and-sumset-extractors.md)
- [Small-bias distribution and generator](../../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Parseval's identity on the Boolean cube](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-parseval.md)
- [Every k-source is a mixture of flat k-sources](../k-sources-are-mixtures-of-flat-sources.md)

## Proof depends on

- [Inner-product extraction above half entropy and the half-entropy barrier](../../non-malleable-extraction-and-explicit-ramsey-graphs/chor-goldreich-inner-product-extractor-and-half-entropy-barrier.md)
- [Fourier spectrum of the inner product mod 2](../../../../Combinatorics/boolean-functions/fourier-expansion-supplements/fourier-spectrum-of-inner-product-mod-2.md)

## Sources

- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- E. Chattopadhyay and J.-J. Liao, "Extractors for Sum of Two Sources", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC 2022), 2022, Definitions 1.2 and 1.8 (arXiv:2110.12652).
- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 230–261, 1988.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
