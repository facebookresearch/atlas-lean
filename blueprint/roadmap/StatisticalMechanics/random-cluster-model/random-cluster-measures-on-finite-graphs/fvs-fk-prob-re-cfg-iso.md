# Isomorphic graphs have equal free FK probabilities after relabelling

Let $G$ and $H$ be simple graphs on finite sets $V$ and $W$, and let $\sigma : V \to W$ be a bijection with $x \sim_G y \iff \sigma(x) \sim_H \sigma(y)$ for all $x, y$. For all $p, q \in \mathbb{R}$ and every configuration $\omega$ on $W$, $\phi_{G,p,q}(\omega^\sigma) = \phi_{H,p,q}(\omega)$, where $\phi$ is the [random-cluster probability](fk-prob.md) and $\omega^\sigma$ is the [pulled-back configuration](re-cfg-iso.md) on $V$, $\omega^\sigma(e) = \omega(\sigma(e))$.
