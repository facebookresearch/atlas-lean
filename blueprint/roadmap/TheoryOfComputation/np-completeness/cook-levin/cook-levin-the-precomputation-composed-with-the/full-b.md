# Step bound of the full machine

For an encoding $E$ of a machine $M$, a list $Y$ of
symbols of the input stack alphabet of $M$, a polynomial $k$ with natural-number coefficients and
$c, e, n \in \mathbb{N}$, write $m = n + 1 + k(n)$ and $T = (m + c)^e$. The bound is
$n + 1 + C + 1 + R$, where $C$ is the step budget of the counter program for $k$, $c$, $e$,
$d = \operatorname{depth} M$ and $n$, and $R$ is the host's step bound for $E$ and $Y$ at $m$
and $T$.

It bounds the number of steps of the full machine on a raw input of length $n$.
