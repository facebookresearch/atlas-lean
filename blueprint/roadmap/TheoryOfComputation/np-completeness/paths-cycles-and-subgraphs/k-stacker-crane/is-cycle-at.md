# Is Cycle At

A list $c$ of moves is a cycle containing the vertex $s$ when each move ends where the next one (cyclically) starts: for every position $j$ of $c$, the destination of the move at position $j$ equals the origin of the move at position $(j + 1) \bmod |c|$, so the last move ends at the origin of the first; and the first move, if any, starts at $s$. The empty list satisfies both conditions vacuously.
