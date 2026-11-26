# Setting two adjacent list positions by a production is a derivation step

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Let $u = u_0 \cdots u_{m-1}$ be a sentential form of $G_M$, let $i + 1 < m$, and let $y_1, y_2$ be
symbols of $G_M$ such that $u_i u_{i+1} \to y_1 y_2$ is a production of $G_M$. Then $u$ derives in $G_M$
the sentential form obtained from $u$ by replacing $u_i$ by $y_1$ and $u_{i+1}$ by $y_2$.
