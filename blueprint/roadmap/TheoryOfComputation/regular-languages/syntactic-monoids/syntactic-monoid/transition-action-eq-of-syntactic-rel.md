# Syntactically equivalent words act identically

Let $M$ be a DFA that is accessible
(every state is reachable from the start state) and state-separated (two states with the same
continuation language are equal). If two words $x$ and $y$ are syntactically equivalent for the
language accepted by $M$, then $x$ and $y$ have the same transition action on $M$: for every
state $q$, reading $x$ from $q$ and reading $y$ from $q$ lead to the same state.
