# Encoding DFA accepts every end-marker encoding

Let $T$ be an alphabet and $\dashv$ an end-marker letter not in $T$; the end-marker encoding of a word $w$ over $T$ is $w\dashv$. The end-marker automaton over $T \cup \{\dashv\}$ has three states, reading (the start state), done (the accepting state) and dead: from reading, a letter of $T$ leads to reading and $\dashv$ leads to done; from done and from dead, every letter leads to dead.
For every word $w$ over $T$, the end-marker automaton started in reading is in done after reading
the encoding $w\dashv$.

## Sources

- J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Addison-Wesley, 2006, Section 6.4.
