# Reachable states of an encoded DFA

For an encoded DFA $D$ over an alphabet $\alpha$ with
decidable equality, the reachable states of $D$ form the list returned by the bounded reachability
search on lists of states started at the start state of $D$, kept inside the states of $D$, in
which the successors of a state $s$ are the states that the transition function of $D$ takes $s$
to on the letters of $D$, in the order of the letters.

A natural number lies in this list exactly when the automaton denoted by $D$ reaches it from its
start state on some word.
