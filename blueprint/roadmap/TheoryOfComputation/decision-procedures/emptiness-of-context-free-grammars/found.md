# Items found by the membership procedure

Let $g$ be an encoded context-free grammar and
$w = w_0 \cdots w_{n-1}$ a word. An item is a triple $(A, i, j)$ of natural numbers, coded as a
natural number by nested pairing. A round sends a list $R$ of items to the items $(A, i, j)$ such
that $A \to X_1 \cdots X_m$ is a production of $g$, $j \le n$, and there are positions
$i = k_0, k_1, \ldots, k_m = j$, each at most $n$, such that for every $t$ with $1 \le t \le m$,
either $X_t$ is the terminal $w_{k_{t-1}}$ and $k_t = k_{t-1} + 1$, or $X_t$ is a nonterminal $B$
with $(B, k_{t-1}, k_t)$ in $R$. The items found are the result of applying the round $M$ times
to the empty list, where $M$ is $(n + 1)^2$ times the length of the list of productions of $g$.
