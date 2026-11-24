# Security of a keyed function family against truth-table distinguishers

Let
$F = (F_n)_{n \in \mathbb{N}}$ be a keyed family of Boolean functions: $F_n(k, x)$ is a Boolean
value for every key $k \in \{0,1\}^{n^2}$ and every input $x \in \{0,1\}^n$. Write $F_{n,k}$ for the
Boolean function $x \mapsto F_n(k, x)$ on $n$ bits and $T(g)$ for the truth table of a Boolean
function $g$. Then $F$ is secure when the following holds for every polynomial $q$ with
natural-number coefficients and every sequence $(D_n)_{n \in \mathbb{N}}$ of functions from
bitstrings to Booleans such that, for each $n$, some circuit given as a list of at most $q(2^n)$
encoded gates has last gate value $D_n(t)$ on every bitstring $t$: for every natural number $c$
there is a natural number $N$ such that for every $n \ge N$

$$\left| \frac{|\{k \in \{0,1\}^{n^2} : D_n(T(F_{n,k})) = \mathrm{true}\}|}{2^{n^2}} -
\frac{|\{g : D_n(T(g)) = \mathrm{true}\}|}{2^{2^n}} \right| \le \frac{1}{2^{nc}},$$

where $g$ ranges over all $2^{2^n}$ Boolean functions on $n$ bits. That is, a distinguisher
computed by circuits of size polynomial in the truth-table size $2^n$ tells a uniformly random
member of the family from a uniformly random Boolean function with advantage at most $2^{-cn}$
for all large $n$, for every $c$.
