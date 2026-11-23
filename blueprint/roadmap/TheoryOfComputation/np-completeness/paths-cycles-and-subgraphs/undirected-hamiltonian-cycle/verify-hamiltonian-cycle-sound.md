# Soundness of the Hamiltonian-cycle verifier

If the Hamiltonian-cycle verifier accepts
the bit strings $x$ and $y$, then, with $m = \lfloor \sqrt{|x|} \rfloor$, we have $|x| = m^2$ and
$m \ge 3$, and there is a simple graph $G$ on the vertices $0, \dots, m - 1$ in which $i$ and $j$
are adjacent exactly when entry $im + j$ of $x$ (counting from $0$) is true, and $G$ has a
Hamiltonian cycle.
