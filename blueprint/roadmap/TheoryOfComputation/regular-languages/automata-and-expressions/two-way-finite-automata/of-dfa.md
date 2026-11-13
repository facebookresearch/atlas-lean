# A DFA as a two-way deterministic automaton

For a DFA $M$ with transition function
$\delta$, this is the deterministic two-way automaton with the same states, start state and
accepting states as $M$ which, in state $q$ reading a symbol $a$, goes to state $\delta(q, a)$
and moves its head one symbol to the right.
