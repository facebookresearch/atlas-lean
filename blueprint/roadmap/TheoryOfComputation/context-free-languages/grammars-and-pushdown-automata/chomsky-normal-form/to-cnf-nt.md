# Encoding symbols as basic nonterminals of the binarized grammar

Let $G$ be a
context-free grammar with nonterminals $N$, and let $t_0, \dots, t_{k-1}$ be the list of
terminals occurring in the production outputs of $G$. This map sends a symbol of $G$ to an
element of $N \sqcup \mathbb{N}$: a nonterminal $A$ goes to $A$, and a terminal $a$ goes to the
least index $i$ with $t_i = a$, or to $k$ if $a$ does not occur in the list.
