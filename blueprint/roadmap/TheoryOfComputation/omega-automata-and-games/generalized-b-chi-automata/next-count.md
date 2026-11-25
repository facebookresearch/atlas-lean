# Counter update for degeneralization

Let $g$ be a generalized Büchi automaton with
acceptance sets $F_0, \dots, F_{k-1}$. The counter update takes a counter value
$i \in \{0, \dots, k\}$ and a state $t$ of $g$ and returns a counter value in $\{0, \dots, k\}$:
if $i < k$, it returns $i + 1$ when $t \in F_i$ and $i$ when $t \notin F_i$; if $i = k$, it
returns $0$.
