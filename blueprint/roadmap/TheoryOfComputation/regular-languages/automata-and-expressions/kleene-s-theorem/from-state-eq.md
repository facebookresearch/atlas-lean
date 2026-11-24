# Equation system satisfied by DFA state languages

Let $\alpha$ be a finite alphabet. Let $M$ be a deterministic automaton with input alphabet $\alpha$, state set $Q$, transition function $\delta$ and set of accepting states $F$. Assume $Q$ is finite. For states $q, j$, the coefficient $A_{qj}$ is the language $\{a : a \in \alpha,\ \delta(q, a) = j\}$ of one-letter words taking $q$ to $j$, and the constant term $B_q$ is $\{\varepsilon\}$ if $q \in F$ and $\emptyset$ otherwise. The language accepted from a state $q$, $X_q$, is the set of words $w$ such that reading $w$ from $q$ ends in an accepting state. Then for every state $q$,

$$X_q = \bigcup_{j \in Q} A_{qj} X_j \cup B_q.$$

From $q$, a word either begins with a letter, after which it continues from the next state, or is empty and $q$ is
accepting.
