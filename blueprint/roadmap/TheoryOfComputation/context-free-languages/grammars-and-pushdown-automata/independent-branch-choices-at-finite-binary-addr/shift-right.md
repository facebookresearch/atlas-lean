# Shifting a configuration to the right subtree

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. The right shift of $\omega \in \Omega$ is its shift by the address
$[\mathrm{true}]$, the configuration $a \mapsto \omega([\mathrm{true}] \cdot a)$ of the right
subtree of the root.
