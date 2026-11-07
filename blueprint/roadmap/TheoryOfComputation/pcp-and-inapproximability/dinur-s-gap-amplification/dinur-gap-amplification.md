# Dinur's gap amplification and alphabet reduction

There exist natural numbers
$S_0, e, d, D, d', V$ and rationals $c, \alpha, c', \alpha'$ with $S_0 \ge 2$, $e \ge 2$, $c > 1$,
$0 < \alpha < 1$, $d \ge 1$, $D \ge 1$, $0 < c' \le 1$, $0 < \alpha' < 1$, $d' \ge 1$ and $V \ge 1$,
and maps $A$ and $R$ from 2CSP instances to 2CSP instances, with the following properties.
Both maps are polynomial-time computable: for each $T \in \{A, R\}$ there is a polynomial-time
computable function $f$ from lists of booleans to lists of booleans such that, for every 2CSP
instance $I$, decoding $f$ applied to the bitstring encoding of $I$ succeeds and returns $T(I)$.
The map $A$ is a gap amplification with constants $c, \alpha, d, D, e$, and $R$ is an alphabet
reduction with constants $S_0, e, c', \alpha', d', V$. Finally, for every 2CSP instance $I$ with
alphabet size at most $S_0$, the instance $J = R(A(I))$ has alphabet size at most $S_0$; if $I$
is well-formed then so is $J$; if some assignment gives $I$ value $1$ then some assignment gives
$J$ value $1$; and for every rational $\delta$ with $0 < \delta \le 1$, if every assignment gives
$I$ value at most $1 - \delta$, then every assignment gives $J$ value at most
$1 - \min(\alpha', c' \min(\alpha, c\delta))$.

The constants $c$ and $c'$ are not tied together: the statement does not assert $c' c > 1$, so
the composed map $R \circ A$ need not enlarge the gap.

## Sources

- I. Dinur, "The PCP theorem by gap amplification", Journal of the ACM 54 (2007), 12:1-12:44 (Proceedings of the Thirty-Eighth Annual ACM Symposium on Theory of Computing, STOC 2006, 241-250).
