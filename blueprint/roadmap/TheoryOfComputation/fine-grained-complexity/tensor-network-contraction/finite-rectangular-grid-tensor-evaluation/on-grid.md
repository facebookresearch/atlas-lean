# Transporting a tensor instance to a grid

Let $R$ be a complete-graph tensor instance on a vertex set $J$ with labels in $A$, let $d \in A$
and let $e : J \to \rho \times \gamma$ be a bijection. The transport of $R$ to the grid is the
instance on $\rho \times \gamma$ whose local tensor at a cell $w$ sends $h : \rho \times \gamma \to
A$ to $R_{e^{-1}(w)}(v \mapsto h(e(v)))$ if $h(w) = d$, and to $0$ otherwise.
