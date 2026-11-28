# Feasible DOUBLE DIGEST instances

A DOUBLE DIGEST instance $(A, B, C)$ is feasible when some orderings $a$ of $A$ and $b$ of $B$ satisfy two tests on their [cut points](cut-points.md) (prefix sums). First, the internal cut points, the prefix sums with their **first and last positions** dropped, are disjoint between $a$ and $b$. Second, the [fragments](fragments.md) of the sorted list of the **distinct** cut points of both orderings agree with $C$ up to permutation. With $A = B = [0, 0]$ and $C = [\,]$ both internal lists are $[0]$, although no coordinate lies strictly inside the interval.
