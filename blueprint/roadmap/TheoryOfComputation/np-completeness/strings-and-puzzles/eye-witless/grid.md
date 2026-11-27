# Grid graph of a puzzle instance

For a puzzle instance given as a list of rows of natural numbers, with $m$ the [number of rows](../corral-bag/rows.md) and $n$ the [length of the first row](../corral-bag/cols.md), the grid graph on the cells $\{0, \dots, m - 1\} \times \{0, \dots, n - 1\}$ is the box product of the path graphs on $\{0, \dots, m - 1\}$ and on $\{0, \dots, n - 1\}$: two cells are adjacent when they share a side.
