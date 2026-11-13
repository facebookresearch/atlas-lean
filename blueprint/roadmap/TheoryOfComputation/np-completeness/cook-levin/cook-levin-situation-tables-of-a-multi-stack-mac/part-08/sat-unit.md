# Unit clauses on run literals are satisfied

Let $M$ be a finite stack machine with
encoding data $E$, let $s$ be an input of $M$, let $T, H \in \mathbb{N}$, and let $V$ be the
number of variables of the layout of $E$ for $T$ and $H$. If $p < V$ is a run literal of $s$ at
height $H$, then the dense clause over $V$ variables whose only literal is $x_p$ is satisfied by
the run assignment of $s$ for $T$ and $H$, which is true exactly on the run literals.
