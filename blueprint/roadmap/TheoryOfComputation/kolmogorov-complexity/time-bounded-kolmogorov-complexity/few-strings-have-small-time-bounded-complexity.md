# Few strings have small time-bounded complexity

For every time bound $t$ and every $s$, fewer than $2^{s}$ strings $x$ satisfy $K^t(x) < s$; in particular at most $2^{s+1} - 1$ strings of any length have $K^t(x) \le s$, and fewer than a $2^{s - n + 1}$ fraction of the truth tables of $\log_2 n$-variable Boolean functions (strings of length $n$) have $K^t \le s$. The same holds for every description method and for $Kt$.

## Proof sketch

Each string of complexity below $s$ has a distinct program of length less than $s$, and there are $2^s - 1$ such programs.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

- [Most strings are incompressible](../incompressible-strings-and-kolmogorov-complexity/card-compressible-lt.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", FOCS 2020.
