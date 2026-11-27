# Activation rules of the LBA grammar

Let $Q$ and $\Gamma$ be finite sets. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. The activation rules are the productions

$$\langle a, x, s, 0, \beta\rangle \to \langle a, x, s, 1, \beta\rangle$$

for all $a \in \Gamma$, all current symbols $x$, all head states $s$ and all boundary tags $\beta$: an
inactive cell becomes active and keeps its other four components.
