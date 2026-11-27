# Productions of the triple grammar

Let $M$ be a pushdown automaton with a finite set of
states, a finite stack alphabet, start state $q_0$ and initial stack symbol $Z_0$, and let $T_0$
be a finite set of input letters. Every production of the triple grammar of $M$ and $T_0$ is of
one of two kinds. Either it is a start production $S \to (q_0, Z_0, q)$ for some state $q$,
where $S$ is the initial nonterminal; or there are states $p$ and $r$, a stack symbol $\gamma$,
an input $a$ that is a letter or $\varepsilon$, a transition of $M$ from $p$ on $a$ popping
$\gamma$ that moves to $r$ and pushes $\gamma_1 \cdots \gamma_k$, and states
$s_1, \dots, s_k$ such that, writing $s_0 = r$, the production is

$$(p, \gamma, s_k) \to a\,(s_0, \gamma_1, s_1)(s_1, \gamma_2, s_2) \cdots (s_{k-1}, \gamma_k, s_k)$$

where $a$ is omitted when it is $\varepsilon$ (for $k = 0$ the production is
$(p, \gamma, r) \to a$).
