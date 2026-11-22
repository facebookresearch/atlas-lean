# DFA recognizing end-marker encodings

Let $T$ be an alphabet and $\dashv$ an end-marker letter not in $T$. The end-marker automaton is the
deterministic finite automaton over $T \cup \{\dashv\}$ with three states, reading, done and dead, start state
reading and accepting state done, and transitions: from reading, a letter of $T$ leads to reading and $\dashv$
leads to done; from done and from dead, every letter leads to dead.

## Sources

- J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Addison-Wesley, 2006, Section 6.4.
