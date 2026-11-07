# Entry label of a one-hot literal routine

For a clause kind $c$ of a cell with $g$ symbol
codes and a natural number $l$, the entry label of literal $l$ of $c$ is the first-stage label
of the routine emitting literal $l$ of $c$ if $l < g$, and the halting label otherwise.

The generator never uses it with $l \ge g$.
