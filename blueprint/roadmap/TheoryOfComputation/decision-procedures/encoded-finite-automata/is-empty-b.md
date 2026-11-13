# Emptiness test for encoded NFAs

For an encoded NFA $N$, the emptiness test is the
Boolean that is true exactly when no state in the list of reachable states of $N$ is an
accepting state of $N$; the reachable states are those reachable from a start state of $N$ by
zero or more moves, each a transition on some letter or an ε-move.
