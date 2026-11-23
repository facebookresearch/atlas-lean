# Degeneralization of a generalized Büchi automaton

Let $g$ be a generalized Büchi
automaton with $k$ acceptance sets. Its degeneralization is the Büchi automaton over the same
alphabet whose states are the pairs $(s, i)$ of a state $s$ of $g$ and a counter value
$i \in \{0, \dots, k\}$. On a symbol $x$ there is a transition from $(s, i)$ to $(s', i')$ iff $g$
has a transition from $s$ to $s'$ on $x$ and $i'$ is the counter update of $i$ at the state $s'$.
The start states are the pairs $(s, 0)$ with $s$ a start state of $g$, and the accepting states
are the pairs $(s, k)$.
