# Walking to a vertex and setting its mark

Let $c$ be a stack other than the mark stack $M$
and the parking stack $P$, and let $\mathit{self}$, $\mathit{back}$, $\mathit{next}$ be labels
such that the marking machine at $\mathit{self}$ is the walk step counted by $c$ that loops at
$\mathit{self}$ and finishes with the mark-setting step to $\mathit{back}$, and at
$\mathit{back}$ it moves the bit block of $P$ onto $M$, looping at $\mathit{back}$ and then
going to $\mathit{next}$. Let $S$ be stacks in which $c$ holds the counter value $j$ (for some
unit symbol), $M$ holds the bits of a list $m$ of booleans, and $P$ is empty. Then from label
$\mathit{self}$ with stacks $S$ and any internal state, the machine reaches label
$\mathit{next}$ in at most $2j + 2$ steps, with some internal state and stacks $S'$ such that
$c$ and $P$ are empty, $M$ holds the bits of $m$ with entry $j$ set to true (unchanged when
$j \ge |m|$), and $S'$ agrees with $S$ on every stack other than $c$, $M$ and $P$.
