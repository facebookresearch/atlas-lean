# Vote after shifting the preferred candidate up in SHIFT BRIBERY for Borda

In SHIFT BRIBERY for Borda, for a list $v$ of natural numbers, a candidate $p$ and a natural number $k$, let $j$ be the zero-based index of the first occurrence of $p$ in $v$, or the length of $v$ if $p$ does not occur in it. The shifted list is obtained by deleting the first occurrence of $p$ from $v$ (nothing, if $p$ does not occur) and inserting $p$ at index $j - k$ of the remaining list, where subtraction is natural-number subtraction, so the index is $0$ when $k \ge j$.

For a vote, which lists every candidate exactly once, this moves $p$ up by $\min(k, j)$ places, and each candidate it passes moves down by one place. On an arbitrary list only the first occurrence of $p$ moves, and $p$ is inserted even when it is absent: then it lands at index $\operatorname{length}(v) - k$, so shifting an absent $p$ by zero appends it.
