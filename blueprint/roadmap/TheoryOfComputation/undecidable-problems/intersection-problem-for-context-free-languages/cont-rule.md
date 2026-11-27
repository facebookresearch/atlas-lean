# The continuation production

For a list $P$ of dominoes, a map $\sigma$ assigning a word
over $\alpha$ to each domino, a nonterminal $A \in \mathbb{N}$ and an index $i \in \mathbb{N}$,
this is the production $A \to w_i\, A\, i$ in encoded form, where $w_i$ is $\sigma$ applied to the
$i$-th domino of $P$ (the domino with both words empty when $i$ is past the end of $P$): its
right-hand side is the letters of $w_i$ as terminals, then the nonterminal $A$, then the index
terminal $i$.
