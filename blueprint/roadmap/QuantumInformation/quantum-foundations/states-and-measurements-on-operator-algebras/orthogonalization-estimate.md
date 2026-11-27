# The orthogonalization estimate from a dilation

Let $(M_a)$ be a measurement in a star-ordered algebra, $\varphi$ a state, $(q_a)$ projections with $q_a$ commuting with $M_a$, $(P_a)$ a projective measurement, and $h$ an element with $0\le h\le1$ such that $h^2 = \sum_aq_aM_a$, $hP_ah = q_aM_a$ for all $a$, and $\varphi(\sum_aM_a^2)\le\varphi(\sum_aq_aM_a)$. Then

$$
\sum_a\|M_a-P_a\|_\varphi^2\le9\Big(1-\sum_a\operatorname{Re}\varphi(M_a^2)\Big).
$$

## Proof sketch

Split $M_a-P_a = (1-q_a)M_a+(h-1)P_ah+P_a(h-1)$ and bound each sum of squared norms by $1-\varphi(\sum_aM_a^2)$ using $x^2\le x$ for $0\le x\le1$: the first sums to at most $1-\varphi(\sum_aq_aM_a)$, the second is at most $\varphi(q_aM_a-(q_aM_a)^2)\le\varphi(M_a-M_a^2)$ per outcome, and the third sums to $\varphi((1-h)^2)\le\varphi(1-h^2)$. Then $(x+y+z)^2\le3(x^2+y^2+z^2)$ gives the factor $9$.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](algebraic-measurements-and-agreement.md)

## Sources

- M. de la Salle, "Orthogonalization of positive operator valued measures", Comptes Rendus. Mathematique 360:549-560, 2022.
