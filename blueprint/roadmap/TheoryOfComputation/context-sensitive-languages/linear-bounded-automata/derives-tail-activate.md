# Tail cells derive their activated encoding

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. Let $w = w_0 \cdots w_{n-1}$ be a word over $\Gamma$ and let $t \ge 1$. Then the sentential form

$$\langle w_0, w_0, \bot, 0, \mathrm{middle}\rangle \cdots \langle w_{n-2}, w_{n-2}, \bot, 0, \mathrm{middle}\rangle\, \langle w_{n-1}, w_{n-1}, \bot, 0, \mathrm{right}\rangle$$

(the empty form if $n = 0$) derives (in finitely many, possibly zero, rewriting steps of $G_M$) the sentential form $\langle w_0, w_0, \bot, 1, \beta(t, n + t)\rangle
\cdots \langle w_{n-1}, w_{n-1}, \bot, 1, \beta(t + n - 1, n + t)\rangle$, where $\beta(h, n)$ denotes the boundary tag of position $h$ on a tape of length $n$ (both if $h = 0$ and $n = 1$; left if $h = 0$ and $n \ne 1$; right if $h \ne 0$ and $h + 1 = n$; middle otherwise).

Since $t \ge 1$, the first of these cells is never tagged left: it is tagged right if it is the last
cell and middle otherwise.
