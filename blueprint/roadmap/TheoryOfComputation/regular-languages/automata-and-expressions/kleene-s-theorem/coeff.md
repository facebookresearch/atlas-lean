# Coefficient in the equation system of a DFA

Let $\alpha$ be a finite alphabet. Let $M$ be a deterministic automaton with input alphabet $\alpha$, state set $Q$, transition function $\delta$ and set of accepting states $F$. For states $q, j \in Q$, the coefficient of $X_j$ in the equation for $X_q$
is the finite union $\bigcup_{a \in \alpha,\ \delta(q, a) = j} \{a\}$, the language of one-letter words $a$ with
$\delta(q, a) = j$.
