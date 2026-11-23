# The 3-COLOR verifier machine

The program of the 3-COLOR verifier, a multi-stack Turing machine on the seven
[stacks](k.md) $X$ (input), $W$ (witness), $N$, $P$, $T$, $U$, $V$, with the verifier's
[labels](lab.md) and a single bit of internal state. *Moving the bit block* of $T$ onto $P$ means
popping $T$ while its top is a bit and pushing each popped bit onto $P$.

- Reading $n$: the [unary reader](read-u.md) onto $N$, with next label the load label.
- Load: the [load step](load-s.md), which moves the first $n$ color codes of $W$ onto $T$,
  rejecting if $W$ runs out or one of these codes is $11$, and then goes to the next label.
- Next: move the bit block of $T$ onto $P$, then go to the edge-start label.
- Edge start: the [edge-loop start](edge-s.md): accept if $X$ is empty, otherwise go on to read
  the edge.
- Reading the endpoints: the unary reader onto $U$, with next label the reader onto $V$, whose
  next label is the joint walk.
- Joint walk: the [joint walk step](walk-s.md).
- For each pair of bits $(a, b)$: the walk towards the endpoint of $U$ holding $(a, b)$ is the
  [one-sided walk step](walk1-s.md) on $U$ with its own label and $(a, b)$, and likewise for $V$.
- Restore: move the bit block of $T$ onto $P$, then go to the edge-start label.
- Accept and reject: halt.
