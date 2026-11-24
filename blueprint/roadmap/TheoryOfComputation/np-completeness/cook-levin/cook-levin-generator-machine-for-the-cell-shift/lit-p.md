# Literal routine of the cell-shift generator

For a situation $i < N$, a stack $k < K$, a
clause kind $c$ and a literal index $l < 3$, this is the program fragment, indexed by the stages
of the literal routine, that emits literal $l$ of clause $c$ in block $(i, k)$. Write $B$ for the
base counter of literal $l$ and $a$ for its constant offset in block $(i, k)$. Started with $Q$
and the scratch counters empty, the routine copies the value $b$ of $B$ into the counter $Q$
through a scratch counter, restoring $B$, and adds $a$, so that $Q = b + a$. It then repeats:
decrement the counter $P$, halting if $P$ is already $0$; compare $P$ with $Q$ through two
scratch counters, restoring both; if they differ, push the absent-slot code $01$ onto the output
and repeat; if they are equal, push the slot code of a literal whose sign is positive exactly
when $l$ is the last literal of $c$. Finally it empties $Q$ and jumps to the routine of literal
$l - 1$, or to the end of the clause when $l = 0$.
