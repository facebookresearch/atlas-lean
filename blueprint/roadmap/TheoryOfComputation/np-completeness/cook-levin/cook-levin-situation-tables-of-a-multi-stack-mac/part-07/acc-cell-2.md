# Accept-cell clauses pin the top output symbol

Let $E$ be an encoding of a finite stack
machine $M$ with output stack $k_1$, $g$ symbol codes and stack numbering $\kappa$, let $\alpha$
be a symbol of stack $k_1$, and let $T, H, x \in \mathbb{N}$ with $x < g$. In the layout of $E$
at height $H$, let $C[t, k, j, z]$ be the variable for stack $k$, depth $j$ and symbol code $z$
at time $t$, and call a variable $v$ true under an assignment $a$ when $v < |a|$ and $a_v$ is
true. If an assignment $a$ satisfies the accept family for $\alpha$ at bounds $T$ and $H$, and
the variable $C[T, \kappa(k_1), 0, x]$ is true under $a$, then $x$ is the code of $\alpha$ for
stack $k_1$.
