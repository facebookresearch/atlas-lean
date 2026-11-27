# Sign-rank of quadratic forms over F2 across a cut

Let $\iota$ be a finite set of coordinates, $q(x) = x^{\mathsf T} Q x$ a quadratic form over $\mathbb{F}_2$ on $\{0,1\}^\iota$, and $(X, X^c)$ a partition of $\iota$. View $M = (-1)^{q}$ as a matrix with rows indexed by $x_X$ and columns by $x_{X^c}$, and let $\rho$ be the rank over $\mathbb{F}_2$ of the cross block $(Q + Q^{\mathsf T})[X, X^c]$. Then for all real vectors $u, v$ indexed by rows and columns, $|u^{\mathsf T} M v| \le \sqrt{2^{|\iota|}/2^{\rho}}\, \|u\|_2 \|v\|_2$, and

$$2^{\rho} \le \mathrm{rk}_\pm\big((-1)^{q}\big)^2.$$

## Proof sketch

Write $q(x) = q_1(x_X) + q_2(x_{X^c}) + x_X^{\mathsf T} B\, x_{X^c}$ with $B = (Q + Q^{\mathsf T})[X, X^c]$; the first two terms (including the diagonal, which is linear over $\mathbb{F}_2$) only multiply rows and columns by signs. For $H_B(a, b) = (-1)^{a^{\mathsf T} B b}$, character orthogonality gives $H_B^{\mathsf T} H_B = 2^{|X|} K$, where $K(b, b') = [B(b + b') = 0]$ is, after grouping columns by cosets of $\ker B$, block-diagonal with all-ones blocks of size $2^{|X^c| - \rho}$, so $\|M\| = \|H_B\| = 2^{(|\iota| - \rho)/2}$, and Forster's theorem gives $\mathrm{rk}_\pm(M) \ge 2^{|\iota|/2} / 2^{(|\iota| - \rho)/2} = 2^{\rho/2}$.

## Depends on

- [Sign-rank of a Boolean matrix](sign-rank-of-a-boolean-matrix.md)

## Proof depends on

- [Forster's sign-rank lower bound](forsters-sign-rank-lower-bound.md)

## Sources

- J. Forster, "A Linear Lower Bound on the Unbounded Error Probabilistic Communication Complexity", Journal of Computer and System Sciences 65(4), 2002.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
