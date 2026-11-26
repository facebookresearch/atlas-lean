# Charged scan for start epsilon productions

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. For a start nonterminal $S$ and a list $r_1, \dots, r_m$ of productions, the epsilon scan is defined
by recursion: for the empty list its value is false and its cost $1$; for $r_1, \dots, r_m$ its value is true
if $r_1$ has left side $S$ and empty right side or the scan of $r_2, \dots, r_m$ is true, and its cost is the
cost of that scan plus $c_n + 6$.
