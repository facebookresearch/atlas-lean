# Weight of currents with a given selected backbone

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings, $x, y \in V$ and $\omega$ a path from $x$ to $y$ in $G$; a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge, its [sources](sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$.
This is

$$Z_\omega = \sum_{\substack{\partial n = \{x, y\} \\ \mathrm{sel}(n) = \omega}} w(n),$$

the sum over the currents on the edges of $G$ with sources $\{x, y\}$ whose [selected backbone](shb-backbone-select.md) is
$\omega$.
