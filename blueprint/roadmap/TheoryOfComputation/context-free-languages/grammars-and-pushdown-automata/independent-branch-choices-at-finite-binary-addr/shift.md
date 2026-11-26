# Shifting a configuration to the subtree below an address

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For an address $u$ and $\omega \in \Omega$, the shift of $\omega$ by $u$ is
the configuration $a \mapsto \omega(u \cdot a)$: it reads the choices in the subtree below $u$.
