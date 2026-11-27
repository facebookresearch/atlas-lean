# Wefts of the gates of an encoded circuit

For a list
$C = (g_0, \dots, g_{m-1})$ of gates encoded as (kind, references) pairs, the list of wefts is
$(w_0, \dots, w_{m-1})$, where $w_j$ is computed from $w_0, \dots, w_{j-1}$ as follows. Write
$g_j = (c, r)$. The weft $w_j$ is $1$ if $c = 3$ or $c = 4$ (an AND or OR gate) and $r$ has
more than $2$ entries, and $0$ otherwise, plus, when $c = 2$, $c = 3$ or $c = 4$, the maximum of
$w_a$ over the entries $a$ of $r$, where $w_a$ is read as $0$ for $a \ge j$ and the maximum
over no entries is $0$.
