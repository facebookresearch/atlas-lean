# Branch and leaf events at one address are disjoint

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For every address $a$, the event $\{\omega : \omega(a) = \mathrm{true}\}$
that $a$ branches and the event $\{\omega : \omega(a) = \mathrm{false}\}$ that $a$ is a leaf are
disjoint.
