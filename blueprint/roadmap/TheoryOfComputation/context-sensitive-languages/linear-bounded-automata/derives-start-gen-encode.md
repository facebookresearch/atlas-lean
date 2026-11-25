# The start symbol derives the generated form of a word

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. Let $w = w_0 \cdots w_{n-1}$ be a nonempty word over $\Gamma$ and let $q_0$ be the initial state
of $M$. Then the one-letter sentential form consisting of the start symbol derives (in finitely many, possibly zero, rewriting steps of $G_M$) the generated
sentential form of $w$: this is $\langle w_0, w_0, q_0, 0, \mathrm{both}\rangle$ if $n = 1$, and
otherwise $\langle w_0, w_0, q_0, 0, \mathrm{left}\rangle$ followed by $\langle w_j, w_j, \bot, 0,
\mathrm{middle}\rangle$ for $0 < j < n - 1$ and by $\langle w_{n-1}, w_{n-1}, \bot, 0, \mathrm{right}\rangle$.
