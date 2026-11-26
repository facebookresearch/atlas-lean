# The early-stopping search finds exactly the reachable states

Let $M$ be a DFA over a
finite alphabet with finitely many states. For every natural number $n$ at least the number of
states of $M$, the early-stopping reachability search for $M$ from the empty set with at most $n$
rounds returns the set of reachable states of $M$.

Since the search stops once a round changes nothing, a generous bound costs nothing.
