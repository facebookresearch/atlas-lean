# Instance value as a sum over half-edge vectors

Let $R$ be a complete-graph tensor instance on a finite linearly ordered vertex set $J$ with labels
in $A$, let $\Lambda$ be a finite set of labels and $d \in A$. The value of $R$ with labels
$\Lambda$ and default $d$ equals

$$\sum_{\ell} \prod_{w \in J} R_w(\ell_w) \prod_{a < b} [\ell_a(b) = \ell_b(a)],$$

where $\ell$ ranges over the families of maps $\ell_w : J \to A$ with $\ell_w(w') \in \Lambda$ for
$w' \ne w$ and $\ell_w(w) = d$, and $[\cdot]$ is $1$ if the equality holds and $0$ otherwise.
