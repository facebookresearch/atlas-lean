# One round of the generating-nonterminal computation

Let a list of productions be given,
each a pair of a nonterminal $A \in \mathbb{N}$ and a right-hand side made of nonterminals and
terminals, together with a list $G$ of nonterminals. One round returns, in order, the left-hand
sides of those productions in whose right-hand side every nonterminal belongs to $G$.
