# The knapsack loop of the verifier

For weights $w$, values $v$, a target $V$, the
remaining capacities, the unread certificate and the unused flags $u$ of the items: for each
capacity $c$ in turn, the next $|u|$ certificate bits form the mask of that knapsack, whose
selected weights must sum to at most $c$, and the selected items are no longer unused. After
the last knapsack, the values of the items that are not unused must sum to at least $V$.
When fewer than $|u|$ certificate bits remain, the missing bits count as false, and the bits left
after the mask of the last knapsack are ignored. The lists $u$, $w$ and $v$ need not have equal
lengths: weights and values at positions $j \ge |u|$ are never selected, and a position
$j < |u|$ past the end of $w$ or $v$ adds nothing to the corresponding sum.

## Sources

- original to this formalization.
