# A walk step with an exhausted counter

Let $c$ be a stack, $\mathit{self}$ a label,
$\mathit{fin}$ a statement and $S$ stacks in which $c$ is empty. For every internal state $v$,
executing from $v$ and $S$ the walk step counted by $c$ that loops at $\mathit{self}$ and
finishes with $\mathit{fin}$ gives the same result as executing $\mathit{fin}$ from internal
state false and the same stacks $S$.
