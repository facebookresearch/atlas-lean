# The generator derives the full tail of cells

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. Let $w = w_1 \cdots w_n$ be a nonempty word over $\Gamma$. Then the one-letter sentential form
consisting of the generator nonterminal derives (in finitely many, possibly zero, rewriting steps of $G_M$) the sentential form

$$\langle w_1, w_1, \bot, 0, \mathrm{middle}\rangle \cdots \langle w_{n-1}, w_{n-1}, \bot, 0, \mathrm{middle}\rangle\, \langle w_n, w_n, \bot, 0, \mathrm{right}\rangle.$$
