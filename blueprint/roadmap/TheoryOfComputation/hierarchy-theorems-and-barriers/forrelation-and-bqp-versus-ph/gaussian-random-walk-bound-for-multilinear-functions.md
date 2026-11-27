# Raz-Tal random walk lemma for multilinear functions on the cube

Let $F : \mathbb{R}^{2N} \to \mathbb{R}$ be multilinear with $|F| \le 1$ on $[-1,1]^{2N}$, and suppose that for every restriction-shift $\rho \in [-1/2, 1/2]^{2N}$ the function $F_\rho(x) := F(\rho + (1 - |\rho|) x)$ (coordinatewise) satisfies $L_{1,2}(F_\rho) \le t$. Then

$$
\big| \mathbb{E}_{z \sim \mathcal{D}}[F(z)] - F(0) \big| \le O\!\left(\frac{\varepsilon\, t}{\sqrt N}\right) + \frac{1}{N} ,
$$

and $F(0)$ equals the expectation of $F$ under the uniform distribution.

## Proof sketch

Write the Gaussian vector as a sum of $T$ independent small Gaussian steps of variance $\varepsilon/T$ and apply them one at a time to the multilinear extension. Odd-order terms vanish in expectation; second-order terms involve $\sum_{i,j}\hat F_\rho(\{i,j\})\mathrm{Cov}(Z_i, Z_j)$, where the covariance between an $X$- and a $Y$-coordinate is $\pm\varepsilon/(T\sqrt N)$ and within blocks is diagonal, contributing $O(\varepsilon t/(T\sqrt N))$ per step. Higher-order terms are negligible for large $T$, and truncation costs at most $1/N$.

## Depends on

- [The Raz-Tal rounded Gaussian forrelation distribution](raz-tal-gaussian-forrelation-distribution.md)
- [Tal's bound on level-l Fourier mass of constant-depth circuits](tal-level-l-fourier-bound-for-constant-depth-circuits.md)

## Sources

- Ran Raz, Avishay Tal, "Oracle separation of BQP and PH", Journal of the ACM 69(4) (2022), STOC (2019); ECCC TR18-107.
