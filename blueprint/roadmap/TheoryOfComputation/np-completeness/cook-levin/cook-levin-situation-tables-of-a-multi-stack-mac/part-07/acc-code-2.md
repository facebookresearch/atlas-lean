# Accept-code clauses pin the (label, state) code

Let $E$ be an encoding of a finite stack
machine $M$ with $A_0$ (label, state) codes, let $\alpha$ be a symbol of the output stack of $M$,
and let $T, H, u \in \mathbb{N}$ with $u < A_0$. In the layout of $E$ at height $H$, let $X[t, w]$
be the label/state variable $w$ at time $t$, and call a variable $v$ true under an assignment $a$
when $v < |a|$ and $a_v$ is true. If an assignment $a$ satisfies the accept family for $\alpha$
at bounds $T$ and $H$, and $X[T, u]$ is true under $a$, then $u$ is the code that $E$ assigns to
the halted label together with the initial state of $M$.
