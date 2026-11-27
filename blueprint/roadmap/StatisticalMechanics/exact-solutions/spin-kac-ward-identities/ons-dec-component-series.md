# Log-coefficient polynomial over the cycles of a decomposition

Let $L > 2$, $a, b \in \{0, 1\}$, $I$ a finite index set, and for each $i \in I$ a closed walk $p_i$ of the [decorated torus graph](../trivalent-decoration-of-the-torus/ons-dec-graph.md) $\mathcal{D}_L$ (vertices the darts of $T_L = (\mathbb{Z}/L\mathbb{Z})^2$; external edges $\{d, \bar d\}$ joining each dart to its reverse, and chain edges $c_{p,i} = \{(p, i), (p, i + 1)\}$, $i \in \{0, 1, 2\}$, joining the four darts at each site $p$) based at a dart $d_i$. The series is

$$\sum_{i \in I} \chi_{a,b}\big([\pi(p_i)]\big)\, X^{E(p_i)},$$

where $X^{E(p_i)}$ is the squarefree monomial of the set $E(p_i)$ of edges traversed by $p_i$, $\pi(p_i)$ is the set of [torus edges underlying $p_i$](ons-walk-original-edges.md), $[F]$ is the [mod 2 homology class](../homology-and-turning-of-loops-on-the-square-latt/ons-even-homology.md) of a torus edge set $F$, $\chi_{a,b}(h) = (-1)^{(1+a)h_1 + (1+b)h_2 + h_1 h_2}$ is the [spin character](../homology-and-turning-of-loops-on-the-square-latt/ons-spin-character.md), and the series are formal power series in commuting variables $X_e$ indexed by the [decorated edges](ons-dec-edge.md) $e$ (unordered pairs of darts of $T_L$), with $X^m = \prod_e X_e^{m(e)}$ for a finitely supported exponent $m$.
