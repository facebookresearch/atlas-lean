# Tail generated sentential form of a word

Let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. For a word $w = w_1 \cdots w_n$ over $\Gamma$, the tail generated sentential form of $w$ is empty
if $n = 0$, and otherwise is $\langle w_1, w_1, \bot, 0, \mathrm{middle}\rangle \cdots \langle w_{n-1},
w_{n-1}, \bot, 0, \mathrm{middle}\rangle\, \langle w_n, w_n, \bot, 0, \mathrm{right}\rangle$.
