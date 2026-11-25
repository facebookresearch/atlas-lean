# Input symbol under the input head

For an input $x$ and a shifted input head position
$p$, the input symbol is the blank if $p = 0$; otherwise it is the entry of $x$ at index $p - 1$
(counting from $0$) if $p - 1 < |x|$, and the blank if $p - 1 \ge |x|$.
