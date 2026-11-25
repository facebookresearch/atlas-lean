# Soundness of ε-production elimination

Let $g$ be a context-free grammar and, for each
nonterminal $A$, let $L_g(A)$ be the language of words $g$ derives from $A$. Then $L_g$ is a
valuation of the grammar obtained from $g$ by eliminating ε-productions: for every production
$A \to \alpha$ of that grammar, the language of $\alpha$ under $L_g$ (the concatenation of the
languages of its symbols, a terminal $a$ denoting $\{a\}$) is contained in $L_g(A)$.
