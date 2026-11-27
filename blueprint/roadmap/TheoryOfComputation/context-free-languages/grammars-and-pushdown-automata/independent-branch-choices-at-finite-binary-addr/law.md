# Independent branch-choice law on binary addresses

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For a real number $p$ with $0 \le p \le 1$, the branch-choice law $\mu_p$ is
the product measure on $\Omega$ under which the choices at different addresses are independent and
each address branches with probability $p$ and is a leaf with probability $1 - p$. The bounds on $p$
are arguments of the definition.
