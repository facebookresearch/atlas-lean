# Büchi emptiness test

For a nondeterministic Büchi automaton with finitely many states and
finitely many symbols, with decidable equality of states, and whose transitions, start states and
accepting states are decidable, the emptiness test returns true exactly when the automaton has no
lasso. It decides this by computing the set of lasso states; by the lasso characterization, it
returns true iff no infinite word is accepted.

With $n$ states, $f$ reachable accepting states and $k$ symbols, the computation performs at most
$f + 1$ reachability closures of $O(n^3 k)$ transition tests each.
