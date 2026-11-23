# Lasso states of a finite Büchi automaton

For a nondeterministic Büchi automaton with
finitely many states, decidable equality of states, a finite alphabet, and decidable transitions,
start set and accepting set, the lasso states form the finite set of accepting states $s$ that are
reachable from some start state in zero or more transitions and lie on a nonempty cycle, that is,
$s$ is reachable from itself in one or more transitions.

The set is computed by one reachability closure from all start states, then one cycle closure for
each reachable accepting state; each closure takes as many rounds as there are states.
