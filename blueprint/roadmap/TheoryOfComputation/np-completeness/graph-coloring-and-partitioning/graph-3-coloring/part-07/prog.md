# The 3-COLOR verifier machine

The verifier is the program on the seven stacks $X$
(input), $W$ (witness), $N$, $P$, $T$, $U$, $V$, with internal state a bit, that runs as follows.
It reads the unary number $n$ off $X$ onto the counter $N$; loads the first $n$ color codes of
$W$ onto $T$, rejecting if $W$ runs out or one of these $n$ codes is $11$; moves the bits on top
of $T$ onto the color stack $P$; and then repeatedly starts an edge, accepting if $X$ is
exhausted and otherwise reading the endpoints $u$ and $v$ in unary onto the counters $U$ and
$V$, walking the colors from $P$ onto $T$ towards both endpoints, and moving the passed colors
back from $T$ onto $P$ before the next edge. Reading a number rejects if $X$ runs out; the walk
rejects if an endpoint has no color or if the two endpoints of a non-loop edge have the same
color. The accepting and rejecting labels halt.
