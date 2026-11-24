# Grammar denoted by an encoding

For an encoded context-free grammar $g$ over $T$, the
context-free grammar over $T$ whose nonterminals are the natural numbers, whose initial
nonterminal is the start nonterminal of $g$, and whose productions are the decodings of the
encoded productions of $g$: an encoded production $(i, u)$ becomes the production rewriting the
nonterminal $i$ to the word obtained from $u$ by reading each entry $\mathrm{inl}\, j$ as the
nonterminal $j$ and each entry $\mathrm{inr}\, a$ as the terminal $a$.
