# Context-free languages

A *context-free grammar* over a type $T$ of terminals consists of a type $N$ of nonterminals, an initial nonterminal and a finite set of rules, each
rewriting one nonterminal to a string of symbols, a symbol being a terminal or a nonterminal. A rule rewrites a string by replacing one occurrence of
its nonterminal by its right-hand side, the grammar *derives* $v$ from $u$ if a finite sequence of such rewrites leads from $u$ to $v$, and its *language*
is the set of words $w \in T^*$ derived from the initial nonterminal. A language $L$ over $T$ is *context-free* if some context-free grammar over $T$ has
language $L$.
