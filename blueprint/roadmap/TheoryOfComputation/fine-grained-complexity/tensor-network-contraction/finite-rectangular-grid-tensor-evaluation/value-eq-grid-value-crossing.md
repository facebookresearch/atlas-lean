# Complete-graph tensor value as a crossing grid evaluation

Let $R$ be a complete-graph tensor instance on a finite linearly ordered vertex set $J$ with labels
in $A$, let $\Lambda$ and $\Delta$ be finite sets of labels, $d \in \Delta$, and let
$e : J \to \rho \times \gamma$ be a bijection onto the cells of a grid with finite linearly ordered
rows $\rho$ and columns $\gamma$. Then the value of $R$ with labels $\Lambda$ and default $d$
equals the grid value, with edge labels $\Lambda$ and diagonal labels $\Delta$, of the transport of
$R$ to the grid along $e$ (with default $d$), using the crossing kernel on every rectangle.

The transport is zero unless the diagonal label is $d$, so other diagonal labels contribute
nothing; $d$ need not belong to $\Lambda$.
