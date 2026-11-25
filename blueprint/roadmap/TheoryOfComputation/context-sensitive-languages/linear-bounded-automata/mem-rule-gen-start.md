# The first generation rule belongs to the LBA grammar

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. For every $a \in \Gamma$, the production $\Sigma \to \langle a, a, q_0, 0, \mathrm{left}\rangle\,
\Theta$ is a production of $G_M$, where $\Sigma$ is the start symbol, $\Theta$ the generator and $q_0$ the
initial state of $M$.
