# Generated sentential form of a word

Let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. For a word $w = w_0 \cdots w_{n-1}$ over $\Gamma$, the generated sentential form of $w$ is empty
if $n = 0$, is $\langle w_0, w_0, q_0, 0, \mathrm{both}\rangle$ if $n = 1$, and otherwise is
$\langle w_0, w_0, q_0, 0, \mathrm{left}\rangle$ followed by $\langle w_j, w_j, \bot, 0,
\mathrm{middle}\rangle$ for $0 < j < n - 1$ and by $\langle w_{n-1}, w_{n-1}, \bot, 0,
\mathrm{right}\rangle$, where $q_0$ is the initial state of $M$.
