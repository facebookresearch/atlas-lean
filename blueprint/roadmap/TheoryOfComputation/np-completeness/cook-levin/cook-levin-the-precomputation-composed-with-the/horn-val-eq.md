# Splitting off the starting accumulator in Horner evaluation

For a list
$c_1, \dots, c_\ell$ of natural numbers and natural numbers $b$ and $A$, write $h(x)$ for the
Horner value of $c_1, \dots, c_\ell$ with base $b$ from accumulator $x$: the number obtained
from the starting value $x$ by replacing the current value $y$ by $y b + c_i$ for
$i = 1, \dots, \ell$ in turn. Then $h(A) = A b^{\ell} + h(0)$.
