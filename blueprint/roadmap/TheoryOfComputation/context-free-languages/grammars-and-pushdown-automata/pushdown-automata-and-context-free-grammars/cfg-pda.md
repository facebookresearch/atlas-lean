# The pushdown automaton simulating a context-free grammar

For a context-free grammar $g$
over an alphabet $T$, this is the pushdown automaton with input alphabet $T$, a single state, the
terminals and nonterminals of $g$ as stack alphabet, and the initial nonterminal of $g$ as initial
stack symbol. Popping a nonterminal $A$ on an $\varepsilon$-transition, it may push the right-hand
side of any production of $g$ with left-hand side $A$ (whose first symbol becomes the new top);
popping a terminal $a$ while reading the input letter $a$, it pushes nothing. It has no other
transitions.
