# Weight of the assignments satisfying a clause

For a weight $\pi(v) \in \mathbb{R}$ on each truth assignment $v$ to the variables $0, \dots, n - 1$ and a clause $C$, the weight of $C$ is

$$P_\pi(C) = \sum_{v \text{ satisfies } C} \pi(v),$$

where variables from $n$ on read as false. The weights are arbitrary real numbers, so $P_\pi(C)$ can be negative or exceed $1$; it is the probability of $C$ only when $\pi$ is nonnegative with total $1$, as in the [feasibility predicate](probabilistic-satisfiability-feasible.md).
