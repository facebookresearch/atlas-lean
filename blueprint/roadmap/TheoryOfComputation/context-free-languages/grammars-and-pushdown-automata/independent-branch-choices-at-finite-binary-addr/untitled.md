# Configurations of branch choices at binary addresses

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. The space $\Omega$ is just this function type; it carries no tree or process
structure.
