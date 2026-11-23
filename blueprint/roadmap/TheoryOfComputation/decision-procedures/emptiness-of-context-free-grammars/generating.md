# Generating nonterminals

For an encoded grammar $g$, start from the empty list of
nonterminals and, in each round, replace the current list $G$ by the list of left-hand sides of
those productions of $g$ whose right-hand sides contain no nonterminal outside $G$. The
generating nonterminals of $g$ are the list obtained after as many rounds as $g$ has productions.

Every nonterminal in this list derives a terminal word, and the start nonterminal is in it
whenever the grammar generates some word.
