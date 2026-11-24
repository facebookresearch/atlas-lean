# Cleanup phase of the SAT verifier host

Fix either value of the 3SAT flag, an answer bit
$b$, a natural number $m$, an internal state $v$, and host stacks $S$ such that every stack of $S$
has length at most $m$ and the output stack of $S$ is empty. Then for some $n \le m + 2$, the host
program runs in exactly $n$ steps from the configuration at the cleanup label with answer $b$,
internal state $v$ and stacks $S$ to the halted configuration with internal state false, the
one-symbol word $b$ on the output stack and every other stack empty.
