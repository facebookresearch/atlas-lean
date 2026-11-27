# Min-Rep reduction: Label Cover to CMMSA, and NP-hardness of GapCMMSA

For a Label Cover instance with $m$ edges and label sets $\beta, \gamma$, introduce a variable $x_{u,a}$ for each left vertex $u$ and $a \in \beta$ of weight $\deg(u)$, a variable $y_{w,b}$ for each right vertex $w$ and $b \in \gamma$ of weight $\deg(w)$, the monotone DNF $\varphi_e = \bigvee_{a \in \beta} (x_{u,a} \wedge y_{w, \pi_e(a)})$ for each edge $e = (u, w)$, and threshold $\theta = 2m$. If the instance is satisfiable then a satisfying assignment of weight $2m$ exists; if every labelling satisfies at most a $\delta < 1/g^2$ fraction of the edges then every satisfying assignment has weight greater than $2gm$. Combined with Label Cover with small soundness, $\mathrm{GapCMMSA}_g$ is NP-hard for every constant $g \ge 1$.

## Proof sketch

A satisfying assignment of weight at most $2gm$ selects label sets $A_u, B_w$ with $\sum_e (|A_u| + |B_w|) \le 2gm$; labelling each vertex uniformly from its selected set satisfies edge $e$ with probability at least $1/(|A_u||B_w|) \ge 4/(|A_u| + |B_w|)^2$, and convexity of $t \mapsto 4/t^2$ yields an expected $m/g^2$ satisfied edges.

## Depends on

- [Collective Minimum Monotone Satisfying Assignment (CMMSA)](collective-minimum-monotone-satisfying-assignment.md)
- [Label Cover (projection games)](label-cover-projection-games.md)

## Proof depends on

- [Label Cover is NP-hard with perfect completeness and arbitrarily small soundness](label-cover-np-hard-with-small-soundness.md)

## Sources

- G. Kortsarz, "On the Hardness of Approximating Spanners", Algorithmica 30(3), 2001.
- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022.
