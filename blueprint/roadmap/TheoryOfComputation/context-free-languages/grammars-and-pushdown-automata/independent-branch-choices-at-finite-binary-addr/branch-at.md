# Branch event at an address

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For an address $a$, the branch event at $a$ is the set of
$\omega \in \Omega$ with $\omega(a) = \mathrm{true}$.
