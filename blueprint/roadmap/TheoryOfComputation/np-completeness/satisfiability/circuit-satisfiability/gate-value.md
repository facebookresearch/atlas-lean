# Value of a gate

Let $x = (x_0, \dots, x_{n-1})$ be an assignment of booleans to the
variables and $v$ the list of values of the earlier gates. An input index $r$ resolves to $x_r$ if
$r < n$, and otherwise to $v_{r-n}$, or to false if that entry does not exist. The value of a gate
$(o, a, b)$ is the conjunction of the resolved inputs $a$ and $b$ if $o = 0$, their disjunction
if $o = 1$, the negation of the resolved input $a$ if $o = 2$, $x_a$ (false if $a \ge n$) if
$o = 3$, true if $o = 4$, and false if $o \ge 5$.
