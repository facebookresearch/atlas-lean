# Touch bits from the pair walk of a vertex

Let $n$ and $v$ be natural numbers, let $m$ be
the number of vertex pairs in encoding order for $n$, and let $b$ be a list of $m$ pair bits. Let
$L$ be the list of vertex marks for $v$ among $n$, let $(x_0, y_0), \dots, (x_{k-1}, y_{k-1})$ be
the pair walk $W(L, [\,])$, and let $c_0, \dots, c_{m-1}$ be the list $b$ reversed. Then the list
of the entries $c_l \wedge (y_l \vee x_l)$ for $l = 0, \dots, \min(k, m) - 1$, reversed, is the
list of the values at $q = 0, 1, \dots, m - 1$ of the test whether pair $q$ touches $v$ under
$b$.
