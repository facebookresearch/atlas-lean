# Finite-address cylinder events

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For a finite set $s$ of addresses and an assignment $t$ of a Boolean to
every address, the cylinder $C(s, t)$ is the set of $\omega \in \Omega$ with $\omega(a) = t(a)$ for
every $a \in s$. Addresses outside $s$ are unrestricted, including the descendants of addresses that
$t$ marks as leaves.
