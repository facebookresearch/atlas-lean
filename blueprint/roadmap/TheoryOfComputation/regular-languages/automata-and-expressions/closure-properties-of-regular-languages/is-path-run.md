# Paths inside one copy of a letter automaton

Let $M$ be a DFA over $T$, and for each
letter $a \in T$ let $N_a$ be a DFA over $T'$. For every state $q$ of $M$, letter $a \in T$,
state $p$ of $N_a$ and word $y$ over $T'$, the ε-NFA built from $M$ and the $N_a$ has a path
reading the letters of $y$, with no ε-moves, from the state $p$ of the copy of $N_a$ entered from
$q$ to the state of the same copy that $N_a$ reaches from $p$ on $y$.
