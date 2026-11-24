# Words with the same transition action are syntactically equivalent

Let $M$ be a DFA over
an alphabet $\Sigma$ and let $L$ be the language accepted by $M$. If two words
$x, y \in \Sigma^*$ have the same transition action on $M$, that is, for every state $q$, running
$M$ from $q$ on $x$ ends in the same state as running $M$ from $q$ on $y$, then $x$ and $y$ are
syntactically equivalent for $L$.
