# Half-edge factored presentation of a tensor instance

Let $R$ be a complete-graph tensor instance on a finite vertex set $J$ with labels in $A$, let
$\Lambda$ be a finite set of labels and $d \in A$. The half-edge presentation of $R$ is the
factored tensor network on $J$ in which

- the allowed states at $v$ are the maps $z : J \to A$ with $z(w) \in \Lambda$ for $w \ne v$ and
  $z(v) = d$ (a label for every half-edge leaving $v$);
- the weight of a state $z$ at $v$ is $R_v(z)$;
- every label set is $\Lambda$;
- the factor on the side of $v$ of the edge to $w$ is $f_{v,w}(z, \theta) = 1$ if
  $z(w) = \theta$ and $0$ otherwise, so the two half-edges of an edge must carry the same label;
- every capacity is $0$.
