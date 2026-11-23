# Position of a literal in a transition clause

Fix a layout with $K$ stacks and window
depth $d$, a height bound $H$, and tables giving for each situation $i$ a current label $a(i)$, a
next label $a'(i)$ and window symbol codes $w(i, k, r)$. The position of literal $j$ of clause
$(t, i)$ is: for $j = 0$, the index of the label/state variable $a(i)$ at time $t$; for
$1 \le j \le Kd$, writing $j - 1 = kd + r$ with $r < d$, the index of the cell variable for stack
$k$, depth $r$ from the top and symbol code $w(i, k, r)$ at time $t$; for $j > Kd$, the index of
the label/state variable $a'(i)$ at time $t + 1$.

The literals of a clause are numbered $0, \dots, Kd + 1$, so the last case is the next label.
