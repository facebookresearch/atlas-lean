# Restoring the parked marks

Suppose the instruction of the marking machine at a label
$\ell$ moves the bits on top of $P$ onto $M$ one at a time, repeating at $\ell$ and continuing at
$\ell'$ once $P$ is empty or its top is not a bit. If $P$ holds the reverse of a bit list $p$ and
$M$ holds a bit list $q$, both as bit symbols, then in exactly $|p| + 1$ steps the machine goes
from $\ell$, with any flag, to $\ell'$, leaving $P$ empty, $M$ holding $p$ followed by $q$, and
every other stack unchanged.
