# The marking algorithm reads the mark of the target

If a bit string $x$ parses as a PATH
instance with source $s$, target $t$, $n$ vertices and edge list $es$, then the marking algorithm
on $x$ returns the mark of $t$ in the reach marks of $s$ (the marks after $n$ marking passes over
$es$, starting from the marks on $0, \dots, n - 1$ with only $s$ marked, and none if $s \ge n$),
where a vertex $t \ge n$ counts as unmarked.

So the checks $s < n$ and $t < n$ of the marking algorithm are implied: a vertex $t \ge n$ has no
mark, and for $s \ge n$ every mark stays cleared.
