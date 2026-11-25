# Syntactic equivalence via transition actions

Let $M$ be a DFA over an alphabet $\Sigma$
that is accessible (every state is reached from the start state by some word) and
state-separated (distinct states have distinct continuation languages), and let $L$ be the
language accepted by $M$. Then two words $x, y \in \Sigma^*$ are syntactically equivalent for $L$
if and only if they have the same transition action on $M$: for every state $q$, running $M$
from $q$ on $x$ ends in the same state as running $M$ from $q$ on $y$.
