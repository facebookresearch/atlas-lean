# Differential formula

Let $G = (V, E)$ be a simple graph on a finite set $V$, let $0 < p_e < 1$ for every unordered pair $e$ of elements of $V$, $q > 0$, $e_0 \in E$, and $g$ a real function of configurations. Then the map $t \mapsto \langle g \rangle_{\mathbf p[e_0 \mapsto t]}$, where $\mathbf p[e_0 \mapsto t]$ replaces $p_{e_0}$ by $t$, is differentiable at $t = p_{e_0}$ with derivative

$$\frac{\mathrm{Cov}_{\mathbf p}(g, \mathbf{1}_{e_0})}{p_{e_0}(1 - p_{e_0})},$$

where $\langle g \rangle_{\mathbf p} = \sum_\omega g(\omega)\, \phi^{\mathbf p}_{G,q}(\omega)$ is the [inhomogeneous expectation](fk-mean-w.md), $\mathrm{Cov}_{\mathbf p}(f, g) = \langle fg \rangle_{\mathbf p} - \langle f \rangle_{\mathbf p} \langle g \rangle_{\mathbf p}$ is the [covariance](fk-cov-w.md), $\phi^{\mathbf p}_{G,q}$ is the [inhomogeneous random-cluster probability](fk-prob-w.md), and $\mathbf{1}_e(\omega)$ is $1$ if $e$ is open in $\omega$ and $0$ otherwise (Grimmett, *The Random-Cluster Model* (2006), Chapter 3).
