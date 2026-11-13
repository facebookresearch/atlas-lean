# Moore's minimal automaton

For a DFA $M$ over a finite alphabet with finitely many states,
Moore's minimal automaton of $M$ has as states the classes of reachable states of $M$ under
Moore's relation. Its start state is the class of the start state of $M$; reading a letter $a$
sends the class of a reachable state $s$ to the class of the state that $M$ reaches from $s$ on
$a$; and the class of $s$ is accepting exactly when $s$ is an accepting state of $M$.

These do not depend on the chosen member $s$, because Moore-related states agree on acceptance
and their successors on each letter are again Moore-related.
