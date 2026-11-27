# Matrix exponentials of exponential-dimension matrices in polynomial depth

There are uniform circuits of depth $\mathrm{poly}(\log D, \log(1/\varepsilon), \log K)$ and size $\mathrm{poly}(D, K, 1/\varepsilon)$ that, given a Hermitian $D \times D$ matrix $H$ with $\|H\| \le K$ and entries specified to $\mathrm{poly}(\log(DK/\varepsilon))$ bits, output a matrix $E$ with $\|E - \exp(H)\| \le \varepsilon$; circuits with the same bounds output an approximate spectral decomposition, a unitary $U$ and a real diagonal $\Lambda$ with $\|H - U\Lambda U^*\| \le \varepsilon$, from which the projection onto the span of the columns of $U$ whose diagonal entries in $\Lambda$ are positive, and normalized traces, are computed. For $D = 2^{\mathrm{poly}(n)}$ the depth is $\mathrm{poly}(n)$.

## Proof sketch

Truncate the power series $\exp(H) = \sum_j H^j/j!$ after $O(K + \log(1/\varepsilon))$ terms. Each matrix product of $D \times D$ matrices is computed in depth $O(\log D)$ by summation trees, and the powers by iterated products, so the total depth is polylogarithmic in $D$, $K$ and $1/\varepsilon$. Approximate spectral decompositions are obtained by computing the characteristic polynomial and null spaces in NC, approximating the roots of the characteristic polynomial to high precision, and orthogonalizing the eigenvectors.

## Depends on

- [The class NC(poly) of polynomial-depth bounded fan-in circuit families](polynomial-depth-circuit-class-nc-poly.md)

## Sources

- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
