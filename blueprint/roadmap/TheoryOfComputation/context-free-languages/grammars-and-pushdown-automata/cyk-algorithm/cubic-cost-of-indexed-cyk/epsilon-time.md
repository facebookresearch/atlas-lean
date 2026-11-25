# Exact cost of the CYK epsilon scan

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. The epsilon scan for a start nonterminal $S$ has value true if and only if some production in the list has left side $S$ and empty right side, with cost $1$ plus $c_n + 6$ per production. For every start nonterminal $S$ and list of $m$ productions, the cost of the epsilon scan is exactly
$1 + m(c_n + 6)$.
