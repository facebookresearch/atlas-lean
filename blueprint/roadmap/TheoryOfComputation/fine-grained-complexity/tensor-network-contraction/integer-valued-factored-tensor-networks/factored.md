# Integer-valued factored tensor network

An integer-valued factored tensor network on a vertex set $J$, with states in a type $\sigma$ and
labels in a type $\tau$, consists of

- for each vertex $a$, a finite set $S_a$ of allowed states;
- for each vertex $a$ and state $z$, an integer weight $W_a(z)$;
- for each pair of vertices $(a, b)$, a finite label set $\Theta_{a,b}$;
- for each pair $(a, b)$, state $z$ and label $\theta$, an integer factor $f_{a,b}(z, \theta)$,
  contributed on the side of $a$ of the edge to $b$;
- for each pair $(a, b)$, a natural-number capacity $c_{a,b}$.

Only the label sets $\Theta_{a,b}$ with $a < b$ are used, and $f_{a,b}$ and $f_{b,a}$ are the two
sides of the same edge. No condition is imposed; in particular capacities need not be symmetric,
and they do not enter the value of the network.
