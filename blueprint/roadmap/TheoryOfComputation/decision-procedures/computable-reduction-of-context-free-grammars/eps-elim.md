# Removing empty productions from an encoded grammar

For an encoded context-free grammar
$g$, the encoded grammar with the same start nonterminal whose productions are, for each
production $A \to u$ of $g$, the productions $A \to v$ for every nonempty word $v$ obtained from
$u$ by deleting some occurrences of nonterminals in the computed list of nullable nonterminals of
$g$.
