# Derivation contexts

Let $g$ be a context-free grammar, let $A$ and $B$ be nonterminals of
$g$, and let $l$ and $r$ be words over the terminal alphabet. Then $(l, r)$ is a derivation
context from $A$ to $B$ when, for every terminal word $w$ that the nonterminal $B$ yields in $g$,
the nonterminal $A$ yields the word $l w r$ in $g$.

This is the language-inclusion form of a one-hole derivation context; it is what pumping
iteration uses, and it holds vacuously when $B$ yields nothing.
