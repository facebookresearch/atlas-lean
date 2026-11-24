# The overlap problem for context-free grammars is recognizable

Let $T$ be an alphabet
with a primitive recursive coding into the natural numbers and decidable equality. For an
encoded context-free grammar $G$ over $T$, write $L(G)$ for the language it generates. The
problem $\mathrm{OVERLAP}_{\mathrm{CFG}}$, the set of pairs $(G, H)$ of encoded context-free
grammars over $T$ such that some word $w$ over $T$ lies in both $L(G)$ and $L(H)$, is
recognizable by a multi-stack machine.

The proof searches for a common word, using that membership in a context-free language is
decidable.
