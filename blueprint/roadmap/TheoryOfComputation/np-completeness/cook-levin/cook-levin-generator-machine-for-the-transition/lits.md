# Literals of a transition clause

For a layout $L$ with $KK$ stacks and window depth $d$,
tables $la$, $na$, $wa$, a height $H$, a time $t$ and a situation $i$, the literals of clause
$(t, i)$ form the list of pairs $(p_j, b_j)$ for $j = 0, 1, \dots, n - 1$, where
$n = KK \cdot d + 2$ is the number of literals, $p_j$ is the position of literal $j$ of clause
$(t, i)$, and the polarity $b_j$ is true exactly when $j = n - 1$. So every literal is negative
except the last one, the next label.
