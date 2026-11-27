# Gate-list circuits for polynomial families

An exact circuit of size at most $s$ for a formal polynomial $f$ over a field $F$ is an indexed list of $s$ polynomial values with some index less than $s$ equal to $f$. Each index is a variable, a scalar from $F$, or the sum or product of two strictly earlier indices. The two indices may coincide, subcomputations may be shared, and variables and scalars count as gates. Values are formal polynomials, not just functions on $F$.

An approximating circuit is an exact circuit over $F((\varepsilon))$ for a polynomial $q$ in the same variables. For every monomial and every integer $i\le0$ the coefficient of $\varepsilon^i$ in its coefficient in $q$ is zero if $i<0$, and is the corresponding coefficient of $f$ if $i=0$. Intermediate gates need not satisfy this condition.

A family $f$ over $F$ assigns to each $n\in\mathbb N$ a polynomial on a finite variable set $V_n$. It is in $\mathrm{VP}$ if for some natural $a$, at every $n$ the cardinality of $V_n$, total degree, and exact gate bound are at most $n^a+a$; in $\overline{\mathrm{VP}}$ use the approximating gate bound and keep the same cardinality and degree conditions. A family belongs to $\mathrm{VNP}$ if for some $r:\mathbb N\to\mathbb N$ there is a $\mathrm{VP}$ family $g_n$ on the disjoint union $V_n\sqcup[ r(n)]$ and

$$
f_n(x)=\sum_{e\in\{0,1\}^{r(n)}}g_n(x,e)
$$

as formal polynomials. The polynomial cardinality bound for the witness family bounds $r(n)$ as well. Substitution uses field elements 0 and 1 even in positive characteristic.

## Expansion

Build bridges to the graph circuit API with explicit size overhead, to the multiplicatively disjoint characterization with polynomial degree bounds, and from the Laurent-series condition to any alternative approximation model before identifying the classes.

## Sources

- Anthropic, [circuit, approximation and family definitions](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L18-L91).
