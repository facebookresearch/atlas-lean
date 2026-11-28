# The MULTIPLE KNAPSACK certificate check

For bit strings $x$ and $w$, the check rejects
when $x$ does not decode. Otherwise $x$ decodes to items with weights $w_j$ and values $v_j$
($j < k$), capacities $c_0, \dots, c_{m-1}$ and a target $V$, and $w$ is read as $m$ masks of
$k$ bits each (missing bits false, bits after the first $mk$ ignored): the check accepts when
every mask selects weights summing to at most its knapsack's capacity and the items selected by
some mask have total value at least $V$.

## Sources

- original to this formalization.
