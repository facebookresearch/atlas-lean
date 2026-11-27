# Simulation rules for a right move

Let $Q$ and $\Gamma$ be finite sets and let $M$ be a linear bounded automaton with state set $Q$, tape
alphabet $\Gamma$ and transition function $\delta$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. The simulation rules of $M$ for right moves are the
productions

$$\langle a, x, q, 1, \beta\rangle\, \langle b, y, \bot, 1, \beta'\rangle \to \langle a, x', \bot, 1, \beta\rangle\, \langle b, y, q', 1, \beta'\rangle$$

for all $q \in Q$, current symbols $x$ and $y$, $a, b \in \Gamma$, boundary tags $\beta, \beta'$ and all
$(q', x', \mathrm{right}) \in \delta(q, x, \beta)$: the head cell writes $x'$ and loses the head and its
right neighbour gains the head in state $q'$, both cells keeping their boundary tags.
