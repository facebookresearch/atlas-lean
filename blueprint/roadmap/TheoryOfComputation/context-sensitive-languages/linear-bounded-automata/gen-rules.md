# Generation rules of the LBA grammar

Let $\Gamma$ be a finite set and let $M$ be a linear bounded automaton with state set $Q$, tape alphabet
$\Gamma$ and initial state $q_0$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. Let $\Sigma$ be the start nonterminal and $\Theta$ the generator
nonterminal. The generation rules of $M$ are, for each $a \in \Gamma$, the four productions

$$\Sigma \to \langle a, a, q_0, 0, \mathrm{left}\rangle\,\Theta,\quad \Sigma \to \langle a, a, q_0, 0, \mathrm{both}\rangle,\quad \Theta \to \langle a, a, \bot, 0, \mathrm{middle}\rangle\,\Theta,\quad \Theta \to \langle a, a, \bot, 0, \mathrm{right}\rangle.$$
