# Curtis–Hedlund–Lyndon theorem on $\mathbb{Z}^d$

Let $S$ be a finite set of states and $d \ge 1$. Give the configuration space $S^{\mathbb{Z}^d}$ the topology of the metric
$\delta(c, e) = 2^{-\min\{\lVert \vec x \rVert_\infty : c(\vec x) \ne e(\vec x)\}}$ (with $\delta(c, c) = 0$; two configurations are close when they agree on a large cube around the origin); its
balls are the *cylinders* $\mathrm{Cyl}(c, r) = \{e : e(\vec x) = c(\vec x) \text{ whenever } \lVert \vec x \rVert_\infty \le r\}$, which are clopen, and the space is
compact. Let $\sigma_1, \dots, \sigma_d$ be the shifts in the $d$ coordinate directions. A map $G : S^{\mathbb{Z}^d} \to S^{\mathbb{Z}^d}$ is the global transition function of
a [cellular automaton](cellular-automata-on-z-d.md) if and only if $G$ is continuous and $\sigma_j \circ G = G \circ \sigma_j$ for $j = 1, \dots, d$ (Hedlund; Curtis and Lyndon). The
one-dimensional case is the [Curtis–Hedlund–Lyndon theorem](../../../Dynamics/topological-symbolic-dynamics/curtis-hedlund-lyndon-theorem/curtis-hedlund-lyndon.md) for the full shift.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.3 (the shifts) and Section 2.7 ("Topology and CA dynamics"), the definitions of the metric and of cylinders, and Theorem 3 (credited there to G. A. Hedlund, *Mathematical Systems Theory* 3 (1969)).
