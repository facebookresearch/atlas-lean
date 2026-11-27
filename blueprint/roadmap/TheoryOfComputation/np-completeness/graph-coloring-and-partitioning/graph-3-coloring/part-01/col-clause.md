# Processing one clause in the 3-COLOR construction

Given a clause $C$ and a state
whose next free vertex is $n$, the literals of $C$ are read from the last one. If $C$ is empty,
the new state has next free vertex $n + 1$, the same earlier occurrences, and the emitted edges
followed by $(n, 0)$, $(n, 1)$, $(n, 2)$, joining the fresh vertex $n$ to the palette vertices
$0$, $1$, $2$. Otherwise let $l$ be the last literal of $C$ and $ls$ the other literals in
reverse order: add an occurrence of $l$, obtaining a state and the literal vertex $L$, then
process the remaining literals $ls$ with output $L$ from that state.
