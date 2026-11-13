# Thompson's construction

To each regular expression $r$ over an alphabet $\alpha$ it assigns
an ε-NFA over $\alpha$ with state set $S(r)$, the states of Thompson's automaton of $r$, by
structural recursion: $0$ goes to the automaton with no states, $\varepsilon$ to the one-state
automaton, a letter $a$ to the single-letter automaton of $a$, $P + Q$ to the union of the
automata of $P$ and $Q$, $PQ$ to their concatenation, and $P^*$ to the star automaton of the
automaton of $P$.
