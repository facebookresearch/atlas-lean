# Setting one list position by a production is a derivation step

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Let $u = u_0 \cdots u_{m-1}$ be a sentential form of $G_M$, let $i < m$, and let $y$ be a symbol of
$G_M$ such that $u_i \to y$ is a production of $G_M$. Then $u$ derives in $G_M$ the sentential form
obtained from $u$ by replacing its entry $u_i$ by $y$.
