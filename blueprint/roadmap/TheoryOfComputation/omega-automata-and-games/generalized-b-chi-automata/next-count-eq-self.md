# The degeneralization counter stays when the awaited set is missed

Let $g$ be a
generalized Büchi automaton with acceptance sets $F_0, \dots, F_{k-1}$ and counter update
$\mathrm{next}$. If $i \in \{0, \dots, k\}$ satisfies $i < k$ and the state $t$ is not in $F_i$,
then $\mathrm{next}(i, t) = i$.
