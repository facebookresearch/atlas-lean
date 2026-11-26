# Membership in a DFA equation coefficient

Let $\alpha$ be a finite alphabet. Let $M$ be a deterministic automaton with input alphabet $\alpha$, state set $Q$, transition function $\delta$ and set of accepting states $F$. For states $q, j$, the coefficient $A_{qj}$ is the language $\{a : a \in \alpha,\ \delta(q, a) = j\}$ of one-letter words taking $q$ to $j$, and the constant term $B_q$ is $\{\varepsilon\}$ if $q \in F$ and $\emptyset$ otherwise. For all states $q, j$ and every word $w$, $w \in A_{qj}$ if and only if
$w$ is a one-letter word $a$ with $\delta(q, a) = j$.
