# Validation phase of the PATH marking machine

Let $w$ be a list of bits, $v$ a Boolean
and $S$ stack contents whose input stack $X$ holds $w$ as bit symbols. Then there are a Boolean
$v'$ and stack contents $S'$ such that, in at most $2|w| + 1$ steps, the machine goes from the
validation label (at a pair) with state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at the
label that walks to the source vertex if $w$ decodes as an edge list, and at the label that
answers false otherwise. The output stack $O$ of $S'$ equals that of $S$. Moreover, if $w$
decodes as an edge list, then $X$ is empty in $S'$, the edge stack $E$ of $S'$ is the reverse
of $w$ as bit symbols followed by the old contents of $E$, and $S'$ agrees with $S$ on every
stack other than $X$ and $E$.
