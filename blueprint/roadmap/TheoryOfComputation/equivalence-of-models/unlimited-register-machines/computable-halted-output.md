# The URM output after a given number of steps is computable

For every URM program $p$,
the function sending an input $x$ and a step count $t$ to the output of $p$ on $x$ after $t$ steps
(nothing while $p$ is still running, the contents of register $0$ once it has halted) is a
computable function of the pair $(x, t)$.

Unbounded search over $t$ then shows that URM evaluation is partial recursive.
