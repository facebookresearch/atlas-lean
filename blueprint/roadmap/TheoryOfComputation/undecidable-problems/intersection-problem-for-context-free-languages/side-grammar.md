# The side grammar of a PCP instance

Let $P = (d_0, \dots, d_{k-1})$ be a list of dominoes
over $\alpha$, let $\sigma$ assign a word over $\alpha$ to each domino, and write
$w_i = \sigma(d_i)$. The side grammar of $\sigma$ and $P$ is the encoded context-free grammar
whose terminals are the letters of $\alpha$ and the index terminals $0, 1, 2, \dots$, whose start
nonterminal is $S = 0$, and whose productions are $S \to w_i \, S \, i$ and $S \to w_i \, i$ for
each $i < k$. Taking for $\sigma$ the top word of a domino gives the top grammar of $P$, and the
bottom word the bottom grammar.
