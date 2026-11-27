# Soundness of the grammar of a regular expression

Let $e$ be an encoded regular
expression. If a sentential form $u$ of the context-free grammar of $e$ yields a terminal word
$w$, then $w$ belongs to the language of $u$: the concatenation, over the symbols of $u$, of
$\{a\}$ for a terminal $a$ and of the language of the regular expression at node $k$ for a
nonterminal $k$.
