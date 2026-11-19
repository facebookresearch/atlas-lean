# Selection indicator of a choice on the variables

Let $G = (V, E)$ be a finite simple graph and $\beta \in \mathbb{R}$, and let $u_e, v_e$ the [chosen endpoints](lee-yang-endpoint0.md) of $e$. For a choice $x = (a, \tau)$ of a Boolean $a_v$ for every vertex $v$ and a pair of Booleans $\tau_e = (\tau_e^0, \tau_e^1)$ for every edge $e$, the variables selected by $x$ are: the
anchor variable $z_v$ when $a_v$ is true; the half-edge variable $w_{u_e, e}$ when $\tau_e^0$ is true;
the half-edge variable $w_{v_e, e}$ when $\tau_e^1$ is true; and no variable $w_{v, e}$ with $v$ not an
endpoint of $e$.
