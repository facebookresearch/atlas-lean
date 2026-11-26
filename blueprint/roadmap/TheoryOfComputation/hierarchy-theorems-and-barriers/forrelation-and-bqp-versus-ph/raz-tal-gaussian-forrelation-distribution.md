# The Raz-Tal rounded Gaussian forrelation distribution

Let $N = 2^n$, $\varepsilon = 1/(24 \ln N)$ and $H_N$ the normalized Walsh-Hadamard matrix ($H_N^2 = I$). Let $(X, Y) \in \mathbb{R}^{N} \times \mathbb{R}^N$ be the centered Gaussian vector with $X \sim \mathcal{N}(0, \varepsilon I_N)$ and $Y = H_N X$. The distribution $\mathcal{D}$ on $\{\pm1\}^{2N}$ is obtained by setting $Z = \mathrm{trnc}(X, Y)$, where $\mathrm{trnc}$ clips each coordinate to $[-1, 1]$, and then independently drawing each output bit $z_i \in \{\pm 1\}$ with $\mathbb{E}[z_i] = Z_i$.

## Depends on

- [Forrelation of two Boolean functions](forrelation-of-two-boolean-functions.md)

## Sources

- Ran Raz, Avishay Tal, "Oracle separation of BQP and PH", Journal of the ACM 69(4) (2022), STOC (2019); ECCC TR18-107.
