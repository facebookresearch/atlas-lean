# Replacing two consecutive symbols is a derivation step

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Let $u, p, q$ be sentential forms and $x_1, x_2, y_1, y_2$ symbols of $G_M$ such that
$u = p x_1 x_2 q$ and $x_1 x_2 \to y_1 y_2$ is a production of $G_M$. Then $u$ derives $p y_1 y_2 q$ in
$G_M$.
