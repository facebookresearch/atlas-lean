# Well-formed Yosenabe instances

A Yosenabe puzzle, given as a list of rows of cell contents $(k, a)$, is well formed when

- it has at least one row and at least one column (the first row is nonempty);
- all rows have the same length;
- every entry has $k \le 2$, and every circle ($k = 1$) has a positive number $a > 0$;
- each gray area has at most one labelled cell: if gray cells $g$ and $g'$ are in the same gray area and both have nonzero label, then $g = g'$.
