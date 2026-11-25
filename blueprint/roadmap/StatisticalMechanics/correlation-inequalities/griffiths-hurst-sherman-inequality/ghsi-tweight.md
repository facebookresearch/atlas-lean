# Inhomogeneous agreement-set Boltzmann weight

Let $G = (V, E)$ be a finite simple graph, $K$ real couplings on unordered pairs and $h \colon V \to \mathbb{R}$ site fields. For configurations $q$ and $a$, with $A_q$ the [agreement set](ghs-lagree-finset.md) of $q$, the agreement-set weight is

$$T_q(a) = \exp\Bigl(\sum_{e \in E,\ e \subseteq A_q} 2K_e\, \sigma_e(a) + \sum_{v \in A_q} 2h_v\, \sigma_v(a)\Bigr),$$

the Boltzmann weight with couplings $2K$ and fields $2h$ on the subgraph induced by $A_q$.
