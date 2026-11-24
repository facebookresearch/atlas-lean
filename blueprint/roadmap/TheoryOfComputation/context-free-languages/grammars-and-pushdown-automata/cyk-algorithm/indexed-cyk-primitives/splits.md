# Charged scan of CYK split positions

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. A table is a finite array of rows, each a finite array of finite lists of nonterminals; for a table $\tau$, the cell $\tau(i, \ell)$ (start $i$, length $\ell$) is entry $i$ of row $\ell$, and the empty list if row $\ell$ or its entry $i$ does not exist. The membership scan of $a \in N$ in a list $x_1 \cdots x_m$ of nonterminals has value true if and only if $a$ is some $x_j$, and is computed by recursion with cost $1$ for the empty list and cost $c_n + 3$ added per entry. For a table $\tau$, $i, \ell \in \mathbb{N}$, nonterminals $B, C$ and a count $k$, the split scan
$\mathrm{split}(\tau, i, \ell, B, C, k)$ examines the split positions $1, \dots, k$ and is defined by recursion:
for $k = 0$ its value is false at cost $1$; for $k + 1$ its value is true if the scan for $k$ is true or both
the membership scan of $B$ in $\tau(i, k + 1)$ and the membership scan of $C$ in $\tau(i + k + 1, \ell - (k + 1))$
are true (truncated subtraction), and its cost is the cost for $k$ plus the costs of these two membership
scans plus $16$.
