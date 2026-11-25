# Agreement-set Boltzmann weight with doubled couplings and field

Let $G = (V, E)$ be a finite simple graph and $\beta, h \in \mathbb{R}$. For configurations $q$ and $a$, with $A_q = \{v : q(v) = +\}$ the [agreement set](ghs-lagree-finset.md) of $q$, the agreement-set weight is

$$T_q(a) = \exp\Bigl(2\beta\Bigl(\sum_{\{u, v\} \in E,\ u, v \in A_q} \sigma_u(a) \sigma_v(a) + h \sum_{v \in A_q} \sigma_v(a)\Bigr)\Bigr),$$

the Boltzmann weight with couplings $2\beta$ and field $2\beta h$ on the subgraph induced by $A_q$.
