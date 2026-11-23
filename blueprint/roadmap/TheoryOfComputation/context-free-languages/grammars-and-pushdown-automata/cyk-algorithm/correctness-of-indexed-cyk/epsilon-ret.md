# Correctness of the CYK epsilon scan

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. The epsilon scan for a start nonterminal $S$ has value true if and only if some production in the list has left side $S$ and empty right side, with cost $1$ plus $c_n + 6$ per production. For every cost $c_n$, start nonterminal $S$ and list of productions, the epsilon scan has value
true if and only if some production of the list has left side $S$ and empty right side.
