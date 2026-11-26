# Preimage of a branch event under a shift

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. Write $\sigma_u \omega$ for the configuration $a \mapsto \omega(u \cdot a)$.
For all addresses $u$ and $a$, the set of $\omega$ such that $\sigma_u \omega$ branches at $a$ is
the set of $\omega$ that branch at $u \cdot a$.
