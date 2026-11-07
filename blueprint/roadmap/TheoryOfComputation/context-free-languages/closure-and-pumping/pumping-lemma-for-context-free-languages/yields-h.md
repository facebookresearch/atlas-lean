# Height-bounded derivations

Let $g$ be a context-free grammar. For a sentential form
$\alpha$ (a list of terminals and nonterminals of $g$), a terminal word $w$ and a natural number
$n$, say that $\alpha$ yields $w$ at height $n$ when this follows from three rules: the empty form
yields the empty word at every height $n$; if $\alpha$ yields $w$ at height $n$, then for every
terminal $a$ the form $a\alpha$ yields $aw$ at height $n$; and if $A \to \beta$ is a production of
$g$, $\beta$ yields $w_1$ at height $n$ and $\alpha$ yields $w_2$ at height $m$, then $A\alpha$
yields $w_1 w_2$ at height $\max(n + 1, m)$.

Thus $n$ bounds the height of a derivation forest, the number of nonterminal expansions along
its longest path; terminals and empty forests contribute nothing.
