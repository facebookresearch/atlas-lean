# Label after a token

Write $w_i$ for the walking label after $i$ literals of the current
clause ($w_3$: three or more). For a Boolean $c$ (whether the filter is capped) and a label
$\ell$, the label reached from $\ell$ on a symbol $s$ is: $w_0$ if $s$ is a clause marker; if $s$
is a literal marker, $w_1$, $w_2$ or $w_3$ when $\ell$ is $w_0$, $w_1$ or $w_2$ respectively, the
failure label when $\ell = w_3$ and $c$ is true, and $\ell$ itself otherwise; and $\ell$ itself
for every other symbol.
