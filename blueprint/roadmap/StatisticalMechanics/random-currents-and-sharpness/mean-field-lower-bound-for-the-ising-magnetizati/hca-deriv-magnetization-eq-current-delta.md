# Random-current form of the $\beta$-derivative of the magnetization

Let $G = (V, E)$ be a finite simple graph, $\beta, h \in \mathbb{R}$ and $o \in V$, let $\langle \sigma_o \rangle_{\beta, h}$ be the finite-volume Ising
magnetization with coupling $1$ and field $h$, and let $G^+$ be the [graph with a ghost vertex](../random-currents-and-the-switching-lemma/with-ghost.md) $\mathfrak g$ joined to every vertex, with coupling $1$ on the edges of $G$ and $h$ on the ghost edges. Then $\beta \mapsto \langle \sigma_o \rangle_{\beta, h}$ has
derivative

$$\frac{1}{Z^2} \Bigl( \sum_{e \in E} \Delta_e + h \sum_{z \in V} \Delta_z \Bigr)$$

at $\beta$, where $Z = \sum_{\partial n = \emptyset} w(n)$ is the sourceless current sum on $G^+$, $\Delta_e$ the
[bond terms](hca-bond-delta.md) and $\Delta_z$ the [field terms](hca-field-delta.md) (M. Aizenman, D. J. Barsky and R. Fernández, *The phase transition in a general class of Ising-type models is sharp*, J. Stat. Phys. 47 (1987) 343–374).
