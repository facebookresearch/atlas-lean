# Reading the mark of a vertex

Let $u \in \mathbb{N}$ and let $m$ be a list of marks.
Start the marking machine at the label `go1`, with any flag, from stacks on which $U$ holds $u$
counter units, $M$ holds $m$ as bit symbols and $P$ is empty. Then within $2u + 2$ steps it
reaches `go2` if the mark of vertex $u$ in $m$ is set and `drV` otherwise (a vertex past the end
of $m$ counts as unmarked), with $U$ and $P$ empty, $M$ holding $m$ again, and every other
stack unchanged.
