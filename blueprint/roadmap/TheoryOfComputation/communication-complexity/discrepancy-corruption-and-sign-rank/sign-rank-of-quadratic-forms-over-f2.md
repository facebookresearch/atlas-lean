# Sign-rank of quadratic forms over F2 across a cut

Let $q(x) = x^{\mathsf T} Q x$ be a quadratic form over $\mathbb{F}_2$ on $\{0,1\}^\iota$ and let $(X, X^c)$ be a partition of the coordinates. View $(-1)^{q}$ as a matrix with rows indexed by $x_X$ and columns by $x_{X^c}$, and let $\rho$ be the rank over $\mathbb{F}_2$ of the cross block $(Q + Q^{\mathsf T})[X, X^c]$. Then its bilinear forms satisfy $|p^{\mathsf T} M q| \le \sqrt{2^{|\iota|}/2^{\rho}}\, \|p\|_2 \|q\|_2$, and

$$2^{\rho} \le \mathrm{rk}_\pm\big((-1)^{q}\big)^2.$$

## Proof sketch

The cross term is a bilinear form of rank $\rho$; Cauchy–Schwarz and character orthogonality along its kernel give the spectral bound $\|M\| \le 2^{(|\iota| - \rho)/2}$ (after normalizing diagonal terms), and Forster's theorem converts it to the sign-rank bound.

## Depends on

- [Sign-rank of a Boolean matrix](sign-rank-of-a-boolean-matrix.md)

## Proof depends on

- [Forster's sign-rank lower bound](forsters-sign-rank-lower-bound.md)

## Sources

- J. Forster, "A Linear Lower Bound on the Unbounded Error Probabilistic Communication Complexity", Journal of Computer and System Sciences 65(4), 2002.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
