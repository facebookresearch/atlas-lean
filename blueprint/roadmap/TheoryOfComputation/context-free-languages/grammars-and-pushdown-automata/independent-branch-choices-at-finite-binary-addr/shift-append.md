# Shifting by a concatenated address

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. Write $\sigma_u \omega$ for the configuration $a \mapsto \omega(u \cdot a)$.
For all addresses $u, v$ and every $\omega$,
$\sigma_{u \cdot v}\, \omega = \sigma_v(\sigma_u \omega)$: shifting by $u \cdot v$ is shifting by
$u$ and then by $v$.
