# A production of a node only produces words of its language

Let $e$ be an encoded
regular expression, $k$ a natural number and $x$ one of the productions of node $k$ built from
the node of $e$ at index $k$. If a word $w$ belongs to the language of the right-hand side of
$x$ (the concatenation, over its symbols, of $\{a\}$ for a terminal $a$ and of the language of
the regular expression at node $i$ for a nonterminal $i$), then $w$ belongs to the language of
the regular expression at node $k$.
