# Sergeev's active-square bound for additive matrix synthesis

Every Boolean $m\times n$ matrix $A$ has an additive circuit over any commutative monoid of size at most

$$
\frac{S(A)}{2\log_2 m}+o\Bigl(\frac{(m+n)^2}{\log_2 m}\Bigr).
$$

## Proof sketch

Cut the columns into strips of width $s\approx\log_2 m$; in each strip precompute all sums of subsets of consecutive column pairs that occur in rows, so that each row's contribution within a strip costs about half its active length divided by $s$; add the strip contributions row by row.

## Depends on

- [Additive circuits and the active square of a Boolean matrix](additive-circuits-and-active-square.md)

## Sources

- Igor S. Sergeev, "A relation between additive and multiplicative complexity of Boolean functions", 2013.
