# Dense clause from a list of literals

Given $V \in \mathbb{N}$ and a list $\ell$ of pairs
$(p, b)$ of a variable index $p$ and a sign $b$, the dense clause over $V$ variables has, for each
$v < V$, slot $v$ equal to the literal $x_v$ if the first pair in $\ell$ with index $v$ is
$(v, \mathrm{true})$, the literal $\neg x_v$ if it is $(v, \mathrm{false})$, and empty if $\ell$
has no pair with index $v$. Pairs with index at least $V$ are ignored.
