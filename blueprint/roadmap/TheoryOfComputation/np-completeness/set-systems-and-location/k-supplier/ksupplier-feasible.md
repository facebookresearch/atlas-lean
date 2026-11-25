# Feasible K-SUPPLIER instances

A K-SUPPLIER instance is feasible when there is a set $S$ of vertices (the suppliers) with total
construction cost $\sum_{s \in S} c(s) \le L$ such that every vertex $v$ has a supplier
$s \in S$ with $w(v) \cdot d(v, s) \le K$. Costs and weights are read from their lists, an index
beyond a list counting as $0$.
