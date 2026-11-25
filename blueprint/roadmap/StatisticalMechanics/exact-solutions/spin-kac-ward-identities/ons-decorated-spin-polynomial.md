# Decorated spin polynomial

For $L > 2$ and $a, b \in \{0, 1\}$, the decorated spin polynomial is

$$\sum_{D} \chi_{a,b}\big([\pi(D)]\big)\, X^D,$$

the sum over the even subgraphs $D$ of the [decorated torus graph](../trivalent-decoration-of-the-torus/ons-dec-graph.md) $\mathcal{D}_L$ (vertices the darts of $T_L = (\mathbb{Z}/L\mathbb{Z})^2$; external edges $\{d, \bar d\}$ joining each dart to its reverse, and chain edges $c_{p,i} = \{(p, i), (p, i + 1)\}$, $i \in \{0, 1, 2\}$, joining the four darts at each site $p$), where $X^D = \prod_{e \in D} X_e$, $\pi(D)$ is the [torus even subgraph corresponding to $D$](ons-original-edges-of-decorated.md), $[F]$ is the [mod 2 homology class](../homology-and-turning-of-loops-on-the-square-latt/ons-even-homology.md) of a torus edge set $F$, and $\chi_{a,b}(h) = (-1)^{(1+a)h_1 + (1+b)h_2 + h_1 h_2}$ is the [spin character](../homology-and-turning-of-loops-on-the-square-latt/ons-spin-character.md).
