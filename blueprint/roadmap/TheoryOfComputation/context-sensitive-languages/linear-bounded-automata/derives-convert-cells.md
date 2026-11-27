# Non-head or accepting cells convert to terminals

Let $Q$ and $\Gamma$ be finite sets, let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$, and let $G_M$ be the grammar of $M$. Write $\langle a, x, s, f, \beta\rangle$ for the cell nonterminal with original symbol $a \in \Gamma$, current symbol $x$ (a letter of $\Gamma$ or the blank $\sqcup$), head state $s$ (a state, or $\bot$ if the head is not on the cell), activity flag $f \in \{0, 1\}$ ($1$ meaning active) and boundary tag $\beta$. Let $(a_1, x_1, s_1, f_1, \beta_1), \dots, (a_k, x_k, s_k, f_k, \beta_k)$ be a finite list of
cell tuples such that for every $i$ the head state $s_i$ is $\bot$ or the accepting state of $M$ and
$f_i = 1$. Then the sentential form $\langle a_1, x_1, s_1, f_1, \beta_1\rangle \cdots \langle a_k, x_k,
s_k, f_k, \beta_k\rangle$ derives (in finitely many, possibly zero, rewriting steps of $G_M$) the terminal word $a_1 \cdots a_k$.
