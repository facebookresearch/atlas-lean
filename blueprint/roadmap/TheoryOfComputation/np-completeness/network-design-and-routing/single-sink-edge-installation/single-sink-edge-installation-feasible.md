# Feasible instances of SINGLE-SINK EDGE INSTALLATION

Consider an instance of SINGLE-SINK EDGE INSTALLATION with vertex count $n$, edge list $E = [(u_0, v_0, l_0), \dots, (u_{m-1}, v_{m-1}, l_{m-1})]$, source list $S = [(s_0, d_0), \dots, (s_{r-1}, d_{r-1})]$, sink $t$, cable-type list $C = [(\kappa_0, c_0), \dots, (\kappa_{q-1}, c_{q-1})]$ of capacities $\kappa_a$ and costs $c_a$ per unit length, and bound $K$. It is feasible when there are, for each source position $k < r$, a list $p_k$ of natural numbers, and, for each edge position $j < m$ and cable-type position $a < q$, a natural number $x_{j,a}$ of cables, such that:

- each $p_k$ has first entry $s_k$ and last entry $t$, has no repeated entries, and any two consecutive entries $y, z$ of $p_k$ satisfy that $(y, z)$ or $(z, y)$ is one of the [endpoint pairs](edge-ends.md) $(u_j, v_j)$;
- for every edge position $j$, the sum of the demands $d_k$ over the source positions $k$ whose list $p_k$ [uses](uses-edge.md) $\{u_j, v_j\}$ (has $u_j$ and $v_j$ as consecutive entries, in either order) is at most the installed capacity $\sum_{a < q} x_{j,a} \kappa_a$;
- the total cost $\sum_{j < m} l_j \sum_{a < q} x_{j,a} c_a$ is at most $K$.

Sources, edges and cable types are indexed by list position, so repeated entries count separately. The lists $p_k$ are lists of natural-number labels, not vertices of $\{0, \dots, n - 1\}$: nothing in this condition requires an entry to be less than $n$. For example, with $n = 0$, no edges, one source $(0, d)$ and sink $0$, the one-entry list $[0]$ serves as $p_0$ (a one-entry list has no consecutive pairs), and the instance is feasible for every $K$.

For a [well-formed](well-formed.md) instance, every endpoint pair, every source and the sink lie in $\{0, \dots, n - 1\}$, so each $p_k$ is a simple path from the source $s_k$ to the sink $t$ in the graph of the endpoint pairs (the one-vertex path $[t]$ when $s_k = t$), and the condition asks for one routing path per source and integral numbers of cables on each edge that carry the demand of every source routed through it, at total cost at most $K$. Feasibility does not include well-formedness; the decision problem requires both.
