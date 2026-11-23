# Generated form derives the initial configuration encoding

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. For a word $w = w_0 \cdots w_{n-1}$ over $\Gamma$ and a configuration $c$ of $M$ with state $q$, tape $x_0 \cdots x_{k-1}$ and head position $h$, the encoding $E_w(c)$ is the sentential form $\langle w_0, x_0, s_0, 1, \beta(0, n)\rangle \cdots \langle w_{m-1}, x_{m-1}, s_{m-1}, 1, \beta(m-1, n)\rangle$ with $m = \min(n, k)$, where $s_j = q$ if $j = h$ and $s_j = \bot$ otherwise, and $\beta(h, n)$ denotes the boundary tag of position $h$ on a tape of length $n$ (both if $h = 0$ and $n = 1$; left if $h = 0$ and $n \ne 1$; right if $h \ne 0$ and $h + 1 = n$; middle otherwise).

For every word $w$ over $\Gamma$ (including the empty word), the generated sentential form of $w$
derives (in finitely many, possibly zero, rewriting steps of $G_M$) $E_w(c_0)$, where $c_0$ is the initial configuration of $M$ on $w$. Here the generated
sentential form of $w = w_0 \cdots w_{n-1}$ is empty if $n = 0$, is $\langle w_0, w_0, q_0, 0,
\mathrm{both}\rangle$ if $n = 1$, and otherwise is $\langle w_0, w_0, q_0, 0, \mathrm{left}\rangle$
followed by $\langle w_j, w_j, \bot, 0, \mathrm{middle}\rangle$ for $0 < j < n - 1$ and by $\langle w_{n-1},
w_{n-1}, \bot, 0, \mathrm{right}\rangle$, with $q_0$ the initial state of $M$.
