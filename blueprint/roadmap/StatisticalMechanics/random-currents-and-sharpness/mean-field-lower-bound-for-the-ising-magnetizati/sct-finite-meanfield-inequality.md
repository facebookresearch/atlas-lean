# Finite-volume mean-field inequality for the Ising model

Let $d, n \in \mathbb{N}$, $\beta > 0$, $h > 0$ and $\varphi_0 \in \mathbb{R}$ with $\varphi_0 \le \varphi_\beta(S)$ for every finite
$S \subseteq \mathbb{Z}^d$ containing the origin, where $\varphi_\beta$ is the [Duminil-Copin–Tassion quantity](../sharpness-of-the-phase-transition-for-the-ising/the-duminil-copin-tassion-point-for-the-ising-mo/phi-ising.md).
With $m_n(\beta, h) = \langle \sigma_0 \rangle_{\Lambda_n, \beta, h}$ the [origin magnetization](sct-origin-mag.md) in the free-boundary box, $c_n$ the [minimal magnetization ratio](sct-lattice-c.md) and $\varepsilon_n$ the
[boundary error](sct-current-boundary-error.md),

$$\frac{\partial}{\partial \beta}\, m_n(\beta, h)^2 \ge 2 c_n \Bigl( \frac{\varphi_0}{\beta} \bigl(1 - m_n(\beta, h)^2\bigr) - \varepsilon_n \Bigr)$$

(H. Duminil-Copin and V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli percolation and the Ising model*, Comm. Math. Phys. 343 (2016) 725–745).
