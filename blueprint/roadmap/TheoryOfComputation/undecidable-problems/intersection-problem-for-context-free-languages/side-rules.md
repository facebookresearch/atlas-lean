# The productions of a side grammar

Let $P = (d_0, \dots, d_{k-1})$ be a list of dominoes
over $\alpha$, let $\sigma$ assign a word over $\alpha$ to each domino, write $w_i = \sigma(d_i)$,
and let $A$ be a nonterminal. The side productions are the list of encoded productions
$A \to w_i \, A \, i$ and $A \to w_i \, i$ for $i = 0, 1, \dots, k - 1$, where the letters of
$w_i$ are terminals and $i$ is an index terminal.
