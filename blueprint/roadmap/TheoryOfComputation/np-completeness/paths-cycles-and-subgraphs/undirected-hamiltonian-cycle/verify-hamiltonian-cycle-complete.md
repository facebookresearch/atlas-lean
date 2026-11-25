# Completeness of the Hamiltonian-cycle verifier

Let $x$ be a bit string and
$m = \lfloor \sqrt{|x|} \rfloor$, suppose $|x| = m^2$, and let $G$ be a simple graph on the
vertices $0, \dots, m - 1$ in which $i$ and $j$ are adjacent exactly when entry $im + j$ of $x$
(counting from $0$) is true. If $G$ has a Hamiltonian cycle, then there is a bit string $y$ of
length $mw$, where $w$ is the least natural number with $m \le 2^w$, such that the
Hamiltonian-cycle verifier accepts $x$ and $y$.
