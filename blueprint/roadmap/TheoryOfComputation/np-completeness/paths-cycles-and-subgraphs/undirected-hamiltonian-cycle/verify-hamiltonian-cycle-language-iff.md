# Certificates exist exactly for Hamiltonian graphs

For every bit string $x$, with
$m = \lfloor \sqrt{|x|} \rfloor$, some bit string $y$ makes the Hamiltonian-cycle verifier accept
$x$ and $y$ if and only if $|x| = m^2$, $m \ge 3$, and there is a simple graph $G$ on the vertices
$0, \dots, m - 1$ in which $i$ and $j$ are adjacent exactly when entry $im + j$ of $x$ (counting
from $0$) is true, and $G$ has a Hamiltonian cycle.
