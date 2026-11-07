# Accept-code clauses

Let $E$ be an encoding of a finite stack machine $M$ with $A_0$
(label, state) codes, let $c^\ast$ be the code that $E$ assigns to the halted label together with
the initial state of $M$, and let $T, H \in \mathbb{N}$. In the layout of $E$ at height $H$, let
$W$ be the row width, $V = (T + 1)W$ the number of variables, and $X[t, u] = tW + u$ the
label/state variable $u$ at time $t$. The accept-code clauses are the CNF formula listing, for
each $u < A_0$ in increasing order, the dense clause over $V$ variables built from the single
literal $X[T, u]$ if $u = c^\ast$ and $\neg X[T, u]$ otherwise.
