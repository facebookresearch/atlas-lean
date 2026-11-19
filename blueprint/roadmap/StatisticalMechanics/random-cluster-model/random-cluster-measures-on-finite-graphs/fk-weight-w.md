# Inhomogeneous random-cluster weight

Let $G = (V, E)$ be a simple graph on a finite set $V$, let $(p_e)$, $e$ ranging over the unordered pairs of elements of $V$, be edge parameters, and $q \in \mathbb{R}$. The weight of a configuration $\omega$ is

$$w^{\mathbf p}_{G,q}(\omega) = \prod_{e \in E} \big(p_e \text{ if } e \text{ open},\ 1 - p_e \text{ if } e \text{ closed}\big) \cdot q^{k(\omega)},$$

where $k(\omega)$ is the [number of open clusters](num-clusters.md) (isolated vertices included).
