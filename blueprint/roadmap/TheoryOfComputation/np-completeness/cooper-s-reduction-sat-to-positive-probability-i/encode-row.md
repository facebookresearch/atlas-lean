# Code of a table row

A row of a node's table, consisting of a list $u$ of parent values and natural numbers $\mathit{num}$ and $\mathit{den}$ (a rational table value $\mathit{num}/\mathit{den}$), is encoded as the unary code of the length of $u$, then the bits of $u$, then the unary codes of $\mathit{num}$ and of $\mathit{den}$, where the unary code of $k$ is $k$ ones followed by a zero.
