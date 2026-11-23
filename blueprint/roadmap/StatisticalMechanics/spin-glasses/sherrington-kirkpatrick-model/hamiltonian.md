# Sherrington–Kirkpatrick Hamiltonian

For $\beta \in \mathbb{R}$, $N \in \mathbb{N}$, couplings $g = (g_{ij})$ and a configuration
$\sigma \in \{-1, 1\}^N$,

$$H_N(\sigma) = -\frac{\beta}{\sqrt N}\sum_{1 \le i < j \le N} g_{ij}\,\sigma_i\sigma_j$$

(Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), (1.1)); for $N = 0$ the sum is empty and $H_0 = 0$. With independent standard
Gaussian couplings, $(H_N(\sigma))_\sigma$ is a centred Gaussian process indexed by the hypercube. Since
$g \mapsto -g$ preserves the law of the couplings, the sign in front of the sum does not change the law
of $H_N$ or of the free energy; it is kept as in the source. Configurations are written as Boolean
vectors, with [spin](spin.md) $+1$ for true and $-1$ for false.
