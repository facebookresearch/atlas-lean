# With an empty waiting list, blocks are the classes of equal continuation languages

Let
$M$ be a DFA and $P$ a list of blocks of states such that $P$ with the empty waiting list
satisfies the invariants of Hopcroft's loop. Then two states $p$ and $q$ lie in a common block of
$P$ if and only if they accept the same continuation languages, that is, $M$ accepts a word from
$p$ exactly when it accepts it from $q$.

With an empty waiting list the invariants say that $P$ is a right congruence refining acceptance.
