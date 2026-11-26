# The terminating production of a side grammar

Let $P = (d_0, \dots, d_{k-1})$ be a list
of dominoes over $\alpha$, set $d_i = (\varepsilon, \varepsilon)$ for $i \ge k$, let $\sigma$
assign a word over $\alpha$ to each domino, and write $w_i = \sigma(d_i)$. For a nonterminal $A$
and a natural number $i$, this is the encoded production $A \to w_i \, i$, whose right-hand side
is the letters of $w_i$ as terminals followed by the index terminal $i$.
