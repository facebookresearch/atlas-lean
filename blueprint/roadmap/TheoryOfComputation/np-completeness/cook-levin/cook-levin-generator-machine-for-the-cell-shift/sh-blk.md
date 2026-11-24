# The shift block of a situation and a stack

Fix a layout with $A$ label variables, $K$
stacks and $g$ symbol codes, the generator's parameters $sa$, $pl$, $cn$, $pu$, and
$T, H, t, i, k \in \mathbb{N}$. Write $p = pl(i, k)$, $c = cn(i, k)$, $W = A + K H g$ for the row
width and $V = (T + 1) W$ for the number of variables. The block is the CNF formula consisting, in
this order, of: for each $u < H - \max(p, c)$ and each $x < g$ (ordered by $u$, then $x$), the
dense clause over $V$ variables with the in-range shift literals for $(t, i, k, u, x)$; for each
$r < c - p$, the dense clause over $V$ variables with the overflow literals for $(t, i, k, r)$;
and for each $j < p$, the dense clause over $V$ variables with the pushed-fill literals for
$(t, i, k, j)$. Subtraction is truncated at $0$.
