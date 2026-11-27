# The root branches with probability p

Let $\Omega$ be the space of all maps $\omega$ from finite binary addresses (lists of Booleans) to
$\{\mathrm{true}, \mathrm{false}\}$; $\omega(a) = \mathrm{true}$ means that the node at address $a$
branches and $\omega(a) = \mathrm{false}$ that it is a leaf. For addresses $u$ and $a$, $u \cdot a$
is their concatenation. For a real number $p$ with $0 \le p \le 1$, let $\beta_p$ be the
Bernoulli($p$) measure on the two Booleans (mass $p$ on true, $1 - p$ on false) and let $\mu_p$ be
the product measure on $\Omega$ under which the coordinates $\omega(a)$ are independent with law
$\beta_p$. The root, the empty address, branches with $\mu_p$-probability $p$.
