# Value of a complete-graph tensor instance

Let $J$ be a finite linearly ordered set, $\Lambda$ a finite set of labels in a type $A$, $d \in A$
a default label and $R$ a complete-graph tensor instance on $J$ with labels in $A$. Its value is
the integer

$$\sum_{\ell} \prod_{v \in J} R_v(\ell_v),$$

where $\ell$ ranges over the edge labelings of the complete graph on $J$ with labels $\Lambda$
and default $d$, and $\ell_v : J \to A$ sends $w$ to $\ell(\min(v, w), \max(v, w))$ (so
$\ell_v(v) = d$).
