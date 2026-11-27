# Stay transitions give simulation rules

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. Let $q, q' \in Q$, let $x, x'$ be current symbols, let $a \in \Gamma$ and let $\beta$ be a
boundary tag. If $(q', x', \mathrm{stay}) \in \delta(q, x, \beta)$, where $\delta$ is the transition
function of $M$, then $\langle a, x, q, 1, \beta\rangle \to \langle a, x', q', 1, \beta\rangle$ is a
production of $G_M$.
