# Arc capacities in directed two-commodity integral flow

For DIRECTED TWO-COMMODITY INTEGRAL FLOW, the capacity $c(u, v)$ of the arc from $u$ to $v$ is the capacity in the **first** arc record, in list order, whose ordered endpoints are $(u, v)$, and $0$ if no record has these endpoints. Two records with the same endpoints need not agree: for the records $(0, 1, 2), (0, 1, 7)$ the capacity is $2$, and in the reverse order it is $7$. Only well-formedness of the instance rules out repeated arcs.
