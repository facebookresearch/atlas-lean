# Cylinders that disagree at an address are disjoint

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For a finite set $s$ of addresses and an assignment $t$, let $C(s, t)$ be
the set of $\omega$ with $\omega(a) = t(a)$ for all $a \in s$. If $a \in s$ and $t_1(a) \ne t_2(a)$,
then $C(s, t_1)$ and $C(s, t_2)$ are disjoint.
