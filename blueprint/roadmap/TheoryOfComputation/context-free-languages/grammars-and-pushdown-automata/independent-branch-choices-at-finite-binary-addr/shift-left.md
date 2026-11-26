# Shifting a configuration to the left subtree

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. The left shift of $\omega \in \Omega$ is its shift by the address
$[\mathrm{false}]$, the configuration $a \mapsto \omega([\mathrm{false}] \cdot a)$ of the left
subtree of the root.
