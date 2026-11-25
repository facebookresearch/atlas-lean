# Zero-field disagreement-set Boltzmann weight

Let $G = (V, E)$ be a finite simple graph and $\beta, h \in \mathbb{R}$. For configurations $q$ and $a$, with $A_q = \{v : q(v) = +\}$ the [agreement set](ghs-lagree-finset.md) of $q$, the disagreement-set weight is

$$U_q(a) = \exp\Bigl(2\beta \sum_{\{u, v\} \in E,\ u, v \notin A_q} \sigma_u(a) \sigma_v(a)\Bigr),$$

the zero-field Boltzmann weight with couplings $2\beta$ on the subgraph induced by $V \setminus A_q$.
