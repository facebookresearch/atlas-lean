# Node of a rational Boolean network

A node of a rational Boolean network consists of a list of parent indices and a table of rows $(u, \mathit{num}, \mathit{den})$, where $u$ is a list of Booleans, to be read as the parents' values in the order of the parent list, and $\mathit{num}, \mathit{den}$ are natural numbers. The quotient $\mathit{num}/\mathit{den}$ is a rational table value; it is the probability that the node is true given $u$ when the row is valid ($0 < \mathit{den}$ and $\mathit{num} \le \mathit{den}$), as in a well-formed network.
