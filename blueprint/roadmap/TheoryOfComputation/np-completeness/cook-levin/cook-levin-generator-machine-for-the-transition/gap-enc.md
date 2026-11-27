# Gap encoding of a dense clause

For a starting slot $m$, a list $\ell$ of literals
$(p, b)$ (variable index $p$, sign $b$) and a number of variables $V$, the gap encoding of $\ell$
from slot $m$ to $V$ is defined by recursion on $\ell$. For the empty list it is $V - m$ copies of
the absent-slot block $01$. For a list whose first literal is $(p, b)$ and whose remaining literals
form the list $r$, it is $p - m$ copies of $01$, then the two-bit slot encoding of the literal
with sign $b$ (the bit $1$ followed by the negation of $b$), then the gap encoding of $r$ from
slot $p + 1$ to $V$. Subtraction is truncated at $0$.

When the positions in $\ell$ are strictly increasing, at least $m$ and less than $V$, this is the
encoding of the slots $m, \dots, V - 1$ of the dense clause over $V$ variables with literals
$\ell$.
