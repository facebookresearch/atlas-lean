# Matrix exponentials of exponential-dimension matrices in polynomial depth

There are uniform circuits of depth $\mathrm{poly}(\log D, \log(1/\varepsilon), \log K)$ and size $\mathrm{poly}(D, K, 1/\varepsilon)$ that, given a Hermitian $D \times D$ matrix $H$ with $\|H\| \le K$ and entries specified to $\mathrm{poly}(\log(DK/\varepsilon))$ bits, output a matrix $E$ with $\|E - \exp(H)\| \le \varepsilon$, and similarly approximate positive-part projections and normalized traces. For $D = 2^{\mathrm{poly}(n)}$ the depth is $\mathrm{poly}(n)$.

## Proof sketch

Truncate the power series of $\exp(H/2^r)$ after $O(\log(K/\varepsilon))$ terms with $2^r \ge K$, then square $r$ times. Each matrix product of $D \times D$ matrices is computed in depth $O(\log D)$ by summation trees, so the total depth is polylogarithmic in $D$ and $1/\varepsilon$. Spectral projections are approximated by polynomial approximations of the sign function, evaluated the same way.

## Depends on

- [The class NC(poly) of polynomial-depth bounded fan-in circuit families](polynomial-depth-circuit-class-nc-poly.md)

## Sources

- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
