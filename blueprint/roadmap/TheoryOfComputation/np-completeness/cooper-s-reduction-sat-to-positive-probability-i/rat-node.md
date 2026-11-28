# Node of a rational Boolean network

A node of a rational Boolean network consists of a list of parent indices and a table of rows $(u, \mathit{num}, \mathit{den})$, where $u$ is a list of Booleans, to be read as the parents' values in the order of the parent list, and $\mathit{num}, \mathit{den}$ are natural numbers. In a raw node, $\mathrm{num}/\mathrm{den}$ is the rational value stored in this row. In a well-formed network there is exactly one row for each parent assignment; its quotient is the conditional probability of true for that assignment.
