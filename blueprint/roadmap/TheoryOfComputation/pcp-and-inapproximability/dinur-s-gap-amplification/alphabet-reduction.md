# Alphabet reduction with given constants

Let $S_0, e, d', V$ be natural numbers and
$c', \alpha'$ rationals. A map $T$ from 2CSP instances to 2CSP instances is an alphabet reduction
with constants $S_0, e, c', \alpha', d', V$ when $S_0 \ge 2$, $e \ge 2$, $0 < c' \le 1$,
$0 < \alpha' < 1$, $d' \ge 1$, $V \ge 1$, and for every 2CSP instance $I$ with $n$ variables,
alphabet size at most $S_0^e$ and $m$ constraints: $T(I)$ has at most $V(n + 1)$ variables,
alphabet size at most $S_0$ and at most $d' m$ constraints; if $I$ is well-formed then so is
$T(I)$; if some assignment gives $I$ value $1$ then some assignment gives $T(I)$ value $1$; and
for every rational $\delta$ with $0 < \delta \le 1$, if every assignment gives $I$ value at most
$1 - \delta$, then every assignment gives $T(I)$ value at most $1 - \min(\alpha', c'\delta)$.

The bounds $S_0 \ge 2$ and $e \ge 2$ give $S_0^e > S_0$, so the reduction must genuinely shrink
the alphabet.
