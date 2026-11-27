# Coding the terminals of an encoded grammar

For a map $\varphi$ from terminals of $T$ to words over $T'$ and an encoded context-free grammar $g$ over $T$, the coded grammar has the same start nonterminal and, for each production of $g$ in order, the production with the same left-hand nonterminal whose right-hand side replaces each terminal $a$ by the terminals of $\varphi(a)$ and keeps each nonterminal. The list of productions is mapped element by element, not re-enumerated or deduplicated.
