# Charged list-membership scan

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. The membership scan of $a \in N$ in a list of nonterminals is defined by recursion: for the empty list
its value is false at cost $1$; for a list $b, x_2, \dots, x_m$ its value is true if $a = b$ or the scan of
$x_2, \dots, x_m$ is true, and its cost is the cost of that scan plus $c_n + 3$. The whole list is always
scanned.
