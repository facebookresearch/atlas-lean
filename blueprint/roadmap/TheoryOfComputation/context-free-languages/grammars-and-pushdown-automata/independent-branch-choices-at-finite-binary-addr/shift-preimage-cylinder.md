# Preimage of a cylinder under a shift

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. Write $\sigma_u \omega$ for the configuration $a \mapsto \omega(u \cdot a)$,
and $C(s, t)$ for the set of $\omega$ with $\omega(a) = t(a)$ for all $a \in s$. For an address $u$,
a finite set $s$ of addresses and an assignment $t$, the set of $\omega$ with
$\sigma_u \omega \in C(s, t)$ is $\{\omega : \omega(u \cdot a) = t(a) \text{ for all } a \in s\}$.
