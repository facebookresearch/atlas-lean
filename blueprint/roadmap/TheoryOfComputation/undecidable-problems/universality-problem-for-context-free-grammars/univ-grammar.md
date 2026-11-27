# The universality grammar

For a finite alphabet $\alpha$ with decidable equality and a list
$P$ of dominoes over $\alpha$, the encoded context-free grammar over $\alpha \oplus \mathrm{Bool}$
with start nonterminal $0$ whose productions are the base productions for $k = |P|$, followed by
the mismatch productions of the top words of $P$ with nonterminal $1$, followed by the mismatch
productions of the bottom words of $P$ with nonterminal $2$.

Its language is the union of the complements of the top and bottom list languages of $P$.
