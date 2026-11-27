# One step of a pushdown automaton

Write a configuration of a pushdown automaton
$M$ as $(q, w, s)$: state $q$, remaining input $w$, and stack $s$ listed from the top.
A configuration $(q, w, \gamma s)$ steps to $(q', w, u s)$ whenever $(q', u)$ is an
$\varepsilon$-transition of $M$ from $q$ with top symbol $\gamma$, and a configuration
$(q, a w, \gamma s)$ steps to $(q', w, u s)$ whenever $(q', u)$ is a transition of $M$
from $q$ on the input letter $a$ with top symbol $\gamma$. There are no other steps: a
step pops the top symbol, consumes at most one input letter, and pushes the list $u$
with its head as the new top.
