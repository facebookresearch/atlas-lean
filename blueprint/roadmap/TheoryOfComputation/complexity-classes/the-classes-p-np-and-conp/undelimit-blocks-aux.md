# Bounded parsing of self-delimiting blocks

Given a bound $n$ and a list of booleans $s$,
the parse returns the empty list of payloads if $s$ is empty. If $s$ is nonempty and $n = 0$ it
fails. If $s$ is nonempty and $n = m + 1$, it parses one self-delimiting block from the front of
$s$, then parses the remaining list with bound $m$, and returns the first payload followed by the
payloads of the rest. It fails if either step fails. So the parse succeeds exactly when $s$ is
the concatenation of at most $n$ self-delimiting blocks, and it returns their payloads in order.
