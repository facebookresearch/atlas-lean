# Transitions of the grammar-simulating pushdown automaton

Let $g$ be a context-free
grammar over an alphabet $T$. To the single state, an input option (a letter of $T$, or none for
an $\varepsilon$-transition) and a popped symbol of $g$ (a terminal or a nonterminal), this
assigns a finite set of pairs of the state and a list of symbols of $g$ to push. Popping a
nonterminal $A$ with no input gives, for each production of $g$ with left-hand side $A$, the pair
pushing its right-hand side. Popping a terminal $b$ while reading the letter $a$ gives the single
pair pushing nothing if $a = b$, and the empty set otherwise. Popping a nonterminal while reading
a letter, or a terminal with no input, gives the empty set.
