# Charged membership scan agrees with list membership

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. The membership scan of $a \in N$ in a list $x_1 \cdots x_m$ of nonterminals has value true if and only if $a$ is some $x_j$, and is computed by recursion with cost $1$ for the empty list and cost $c_n + 3$ added per entry. For every cost $c_n$, every $a \in N$ and every list $x$ of nonterminals, the membership scan of
$a$ in $x$ has value true if and only if $a$ occurs in $x$.
