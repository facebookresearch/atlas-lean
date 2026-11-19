# Alphabet padding of a tensor instance

Let $R$ be a complete-graph tensor instance on a finite vertex set $J$ with labels in $A$, let
$d \in A$, let $D$ be a finite set of names in a type $A'$ and $\delta : A' \to A$ a renaming. The
padding of $R$ is the instance on $J$ with labels in $A'$ whose local tensor at $v$ sends
$\theta : J \to A'$ to $R_v(h)$ if $\theta(w) \in D$ for every $w \ne v$, where $h(v) = d$ and
$h(w) = \delta(\theta(w))$ for $w \ne v$, and to $0$ otherwise.
