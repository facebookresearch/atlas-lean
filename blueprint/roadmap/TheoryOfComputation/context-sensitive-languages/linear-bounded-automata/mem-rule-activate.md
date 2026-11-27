# The activation rule belongs to the LBA grammar

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. For every $a \in \Gamma$, current symbol $x$, head state $s$ and boundary tag $\beta$, the
production $\langle a, x, s, 0, \beta\rangle \to \langle a, x, s, 1, \beta\rangle$ is a production of $G_M$.
