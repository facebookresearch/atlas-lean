# Production of the triple grammar for a transition

Let $p$ and $r$ be states, $\gamma$ a
stack symbol, $a$ an optional input letter, $\varepsilon_1 \cdots \varepsilon_k$ a list of stack
symbols and $s_1, \dots, s_m$ a list of states. Write $s_0 = r$ and let $q = s_m$ be the last
state of the list $s_0, s_1, \dots, s_m$ (so $q = r$ when $m = 0$). The production has
left-hand side the nonterminal $(p, \gamma, q)$, and its right-hand side is the letter $a$
(nothing if $a$ is absent) followed by the nonterminals $(s_{i-1}, \varepsilon_i, s_i)$ for
$i = 1, \dots, \min(k, m)$ in order.

It encodes a transition that in state $p$, reading $a$ (or no letter), pops $\gamma$, moves to
state $r$ and pushes $\varepsilon_1 \cdots \varepsilon_k$; the triple grammar uses it with
$m = k$.
