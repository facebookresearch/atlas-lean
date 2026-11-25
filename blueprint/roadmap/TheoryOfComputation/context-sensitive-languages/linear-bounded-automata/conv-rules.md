# Conversion rules of the LBA grammar

Let $\Gamma$ be a finite set and let $M$ be a linear bounded automaton with state set $Q$, tape alphabet
$\Gamma$ and accepting state $q_{\mathrm{acc}}$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. The conversion rules of $M$ are the productions

$$\langle a, x, q_{\mathrm{acc}}, 1, \beta\rangle \to a \qquad\text{and}\qquad \langle a, x, \bot, 1, \beta\rangle \to a$$

for all $a \in \Gamma$, all current symbols $x$ and all boundary tags $\beta$. An active cell becomes its
original terminal; the cell carrying the head converts only in the accepting state, and the boundary tag
is discarded.
