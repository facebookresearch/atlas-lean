# Differential formula in $\beta$

Let $G = (V, E)$ be a simple graph on a finite set $V$, let $J_e > 0$ for every unordered pair $e$ of elements of $V$, $\beta > 0$, $q > 0$, and $g$ a real function of configurations. With $p_e(\beta) = 1 - e^{-\beta J_e}$ the [edge parameters](beta-params.md), the map $b \mapsto \langle g \rangle_{\mathbf p(b)}$ is differentiable at $\beta$ with derivative

$$\sum_{e \in E} \frac{J_e}{p_e(\beta)}\, \mathrm{Cov}_{\mathbf p(\beta)}(g, \mathbf{1}_e),$$

where $\langle g \rangle_{\mathbf p} = \sum_\omega g(\omega)\, \phi^{\mathbf p}_{G,q}(\omega)$ is the [inhomogeneous expectation](fk-mean-w.md), $\mathrm{Cov}_{\mathbf p}(f, g) = \langle fg \rangle_{\mathbf p} - \langle f \rangle_{\mathbf p} \langle g \rangle_{\mathbf p}$ is the [covariance](fk-cov-w.md), $\phi^{\mathbf p}_{G,q}$ is the [inhomogeneous random-cluster probability](fk-prob-w.md), and $\mathbf{1}_e(\omega)$ is $1$ if $e$ is open in $\omega$ and $0$ otherwise (Grimmett, *The Random-Cluster Model* (2006), Chapter 3).
