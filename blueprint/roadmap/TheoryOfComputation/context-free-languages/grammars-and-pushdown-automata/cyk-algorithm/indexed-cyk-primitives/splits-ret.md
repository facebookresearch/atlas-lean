# Successful CYK split scans find a split in range

Let $T$ be a set of terminals and $N$ a set of nonterminals, and let $c_t, c_n \in \mathbb{N}$ be the costs charged for a terminal comparison and for a nonterminal comparison. A costed computation returns a value together with a cost in $\mathbb{N}$. A table is a finite array of rows, each a finite array of finite lists of nonterminals; for a table $\tau$, the cell $\tau(i, \ell)$ (start $i$, length $\ell$) is entry $i$ of row $\ell$, and the empty list if row $\ell$ or its entry $i$ does not exist. The membership scan of $a \in N$ in a list $x_1 \cdots x_m$ of nonterminals has value true if and only if $a$ is some $x_j$, and is computed by recursion with cost $1$ for the empty list and cost $c_n + 3$ added per entry. Let the split scan be defined by $\mathrm{split}(\tau, i, \ell, B, C, 0)$ is false and
$\mathrm{split}(\tau, i, \ell, B, C, k + 1)$ true if and only if $\mathrm{split}(\tau, i, \ell, B, C, k)$ is true or both
$B \in \tau(i, k+1)$ and $C \in \tau(i + k + 1, \ell - (k + 1))$ (as decided by membership scans). Then for all
$\tau, i, \ell, B, C, k$, the value of $\mathrm{split}(\tau, i, \ell, B, C, k)$ is true if and only if there is $k'$
with $0 < k' \le k$, $B \in \tau(i, k')$ and $C \in \tau(i + k', \ell - k')$, where $\ell - k'$ is truncated
subtraction.
