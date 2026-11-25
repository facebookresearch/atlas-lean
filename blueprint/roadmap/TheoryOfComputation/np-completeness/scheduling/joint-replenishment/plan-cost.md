# Plan Cost

The cost of the ordering plan $x$, where $x_{a,t}$ is the quantity of item $a$ ordered in period
$t$: the major cost $K_0$ for each period in which some item is ordered, plus the minor cost
$k_a$ for each period in which item $a$ is ordered, plus, for each item $a$ and period $t$,
$h_a$ times the stock at the end of period $t$. The stock is the cumulative quantity ordered
minus the cumulative demand, computed in truncated natural-number subtraction (so a shortfall
counts as stock $0$); for a plan without backlogging it is the actual stock.
