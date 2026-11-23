# Domination condition fails on the triangle

Consider the triangle on the vertices $0, 1, 2$ with its three [edges](ahd-tri-ends.md), the single
current $m$ made of all three edges, the sites $o = 0$, $x = 1$, $y = 2$, the weight $\varphi \equiv 1$
and the source set $\partial m = \emptyset$ (every vertex has degree $2$). The
[conditioned domination condition](atb-conditioned-dom.md) for the set of currents $\{m\}$ fails:

$$2 \sum_{m \text{ connects all three pairs}} \mathrm{mass}_m(\emptyset) = 2 \cdot 2 > 0 = \sum_{m \text{ connects none of the pairs}} \mathrm{mass}_m(\emptyset),$$

since $m$ connects every pair of vertices and has exactly two sourceless sub-currents, $\emptyset$ and
$m$.
