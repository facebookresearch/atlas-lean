# Depths of the gates of an encoded circuit

For a list
$C = (g_0, \dots, g_{m-1})$ of gates encoded as (kind, references) pairs, the list of depths is
$(d_0, \dots, d_{m-1})$, where $d_j$ is computed from $d_0, \dots, d_{j-1}$ as follows. Write
$g_j = (c, r)$. If $c = 0$ or $c = 1$ (an input or constant gate), then $d_j = 0$; otherwise
$d_j$ is one plus the maximum of $d_a$ over the entries $a$ of $r$, where $d_a$ is read as $0$
for $a \ge j$ and the maximum over no entries is $0$.
