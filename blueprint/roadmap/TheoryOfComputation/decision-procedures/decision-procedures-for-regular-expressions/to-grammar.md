# The grammar of an encoded regular expression

For an encoded regular expression $e$ with
$n$ nodes, its grammar is the encoded context-free grammar with start nonterminal $n - 1$
(truncated subtraction, so $0$ when $n = 0$), in which nonterminal $k$ stands for node $k$. Its
productions are, for each node $k < n$: none if node $k$ is $0$; $k \to \varepsilon$ if it is
$\varepsilon$; if it is the letter $a$, the production $k \to a$; if it is the sum of nodes $i$
and $j$, the productions $k \to i$ (when $i < k$) and $k \to j$ (when $j < k$); if it is the
product of nodes $i$ and $j$, the production $k \to i\,j$ (when $i < k$ and $j < k$); and if it
is the star of node $i$, the productions $k \to \varepsilon$ and $k \to i\,k$ (when $i < k$).
There are no other productions.
