# Linear combination of period vectors

The linear combination of a list of period vectors with a
coefficient list `c`: pair the two lists position by position and
sum the scaled periods, and reject mismatched lengths by
returning `0` (the length guard is checked up front, before the
recursion, so a shorter coefficient list cannot silently truncate
and a longer one cannot silently drop coefficients). Coefficients
are indexed by *position* in `P`, not by period value, so duplicate
periods get independent coefficients: for `P = [p, p]`,
`linComb P [1, 0] = p`, not `2 • p`.

## Sources

- Parikh, "On context-free languages", Journal of the ACM 13 (1966), 570-581.
