# Inner wired domination for vertex sets of $\mathbb{Z}^d$

Let $d \in \mathbb{N}$, let $S_{\mathrm{in}}$ and $S_{\mathrm{out}}$ be finite sets of sites of $\mathbb{Z}^d$, each carrying the nearest-neighbour graph induced from $\mathbb{Z}^d$, and let $\iota : S_{\mathrm{in}} \to S_{\mathrm{out}}$ satisfy $\iota(x) = x$ as sites of $\mathbb{Z}^d$ (so $\iota$ is injective). Let $\partial_{\mathrm{out}} \subseteq S_{\mathrm{out}}$ and $\partial_{\mathrm{in}} \subseteq S_{\mathrm{in}}$ be boundary sets such that no $\iota(x)$ lies in $\partial_{\mathrm{out}}$, and every $x \in S_{\mathrm{in}}$ having a nearest neighbour $z \in \mathbb{Z}^d \setminus S_{\mathrm{in}}$ lies in $\partial_{\mathrm{in}}$. Let $0 < p < 1$ and $q \ge 1$. For every increasing set $A$ of configurations on $S_{\mathrm{in}}$,

$$\sum_{\rho :\ \rho|_{\mathrm{in}} \in A} \phi^w_{S_{\mathrm{out}},\partial_{\mathrm{out}}}(\rho) \le \phi^w_{S_{\mathrm{in}},\partial_{\mathrm{in}}}(A),$$

where $\phi^w_{S,\partial}$ is the [wired random-cluster probability](../finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) of the nearest-neighbour graph on $S$ with boundary $\partial$, $\rho|_{\mathrm{in}}(e) = \rho(\iota e)$ is the [restriction](ocd-inner-restrict.md), and $\mu(A) = \sum_{\omega \in A} \mu(\omega)$.
